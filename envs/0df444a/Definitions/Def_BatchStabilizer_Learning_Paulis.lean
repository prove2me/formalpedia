-- Prove2me | Definitions.Def_BatchStabilizer_Learning_Paulis
-- name    : BatchStabilizer_Learning_Paulis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:21.153001+00:00
-- url     : https://prove2.me/theorems/92aaf4c2-3a15-49ef-b250-729a80555645
-- title:
--   §§3.2–3.3, §4.2 — Pauli labels, Hermitian Paulis $W_u$, isotropic spaces, affine filters $A_L$, syndrome projectors
-- statement:
--   Binary Pauli labels are pairs $u=(a,b)\in\mathbb F_2^n\times\mathbb F_2^n$ (X-part first) with the symplectic form $\langle (a,b),(a',b')\rangle=a\cdot b'+b\cdot a' \pmod 2$ and the quadratic form $Q(a,b)=a\cdot b\pmod 2$. The Hermitian Pauli operator of $u$ is
--   $$W_{(a,b)}=i^{\sum_j a_jb_j}X^aZ^b,\qquad (X^aZ^b)_{x,y}=\mathbf 1\{x=y+a\}(-1)^{b\cdot y},$$
--   where the exponent of $i$ uses the integer lifts of the bits. For a matrix $\rho$ write $\operatorname{tr}(\rho W_u)$ (real part) for the Pauli expectation and $\operatorname{tr}(\rho^2)$ for the purity.
--
--   A binary subspace $T\subseteq\mathbb F_2^{2n}$ is isotropic if the symplectic form vanishes on it (any dimension $0\le r\le n$); it is full if moreover $\dim T=n$ (the published Lagrangian predicate). The symplectic dual is $T^\perp=\{v:\langle v,t\rangle=0\ \forall t\in T\}$ and the affine filter (syndrome coset) of a subspace $L$ is
--   $$A_L=\{m\in\mathbb F_2^{2n}:\langle m,t\rangle=Q(t)\text{ for all }t\in L\},$$
--   which depends only on $L$, not on stabilizer signs. For labels $b_1,\dots,b_r$ and signs $c\in\mathbb F_2^r$ the Hermitian generators are $G_j=(-1)^{c_j}W_{b_j}$, the syndrome projector of $s\in\mathbb F_2^r$ is $\Pi_s=\prod_{j=1}^r(I+(-1)^{s_j}G_j)/2$ (product in the order $j=1,\dots,r$), and $p_s=\operatorname{tr}(\rho\Pi_s)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Labels reuse the published `CutRankSched.Pauli` and `CutRankSched.symp`; matrices are the published `Op (Qubits n)` with basis indexed by Boolean strings, converted to $\mathbb F_2^n$ by `ofQubits`/`toQubits`.
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 9–10, 12–14 (PDF p. 10–11, 13–15), §3.2, §3.3, equations (30), (31), (50)

import Mathlib
import Definitions.Def_ArbLindbladLearn_Stab
import Definitions.Def_CutRankSched_symp
import Definitions.Def_StabTestMem_IsLagrangian

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
noncomputable section

namespace BatchStabilizer.Learning

open LindbladTolerant.Testing

/-! Binary Pauli labels, Hermitian Paulis, isotropic subspaces and syndrome projectors
(Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), §§3.2–3.3, printed pp. 9–10
(PDF pp. 10–11), and §4.2, printed pp. 12–13 (PDF pp. 13–14)). -/

/-- A binary Pauli label `u = (a, b) ∈ F₂ⁿ × F₂ⁿ` (X-part first): the published
`CutRankSched.Pauli n`. -/
abbrev Label (n : ℕ) : Type := CutRankSched.Pauli n

/-- The symplectic inner product `⟨(a,b),(a',b')⟩ = a·b' + b·a'` (mod 2), §3.2: the
published `CutRankSched.symp`. -/
abbrev symp {n : ℕ} (u v : Label n) : ZMod 2 := CutRankSched.symp u v

/-- The binary quadratic form `Q(a,b) = a·b` (mod 2), §3.2. -/
def Q {n : ℕ} (u : Label n) : ZMod 2 := u.1 ⬝ᵥ u.2

/-- The sign `(-1)^z` of a bit `z ∈ F₂`, as a real number. -/
def signZ (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

/-- The bit `0/1 ∈ F₂` of a Boolean computational-basis coordinate. -/
def bitOf (x : Bool) : ZMod 2 := if x then 1 else 0

/-- The computational-basis string `x ∈ {0,1}ⁿ` with bits given by `v ∈ F₂ⁿ`. -/
def toQubits {n : ℕ} (v : Fin n → ZMod 2) : Qubits n := fun j => decide (v j = 1)

/-- The bit vector `x ∈ F₂ⁿ` of a computational-basis string. -/
def ofQubits {n : ℕ} (x : Qubits n) : Fin n → ZMod 2 := fun j => bitOf (x j)

/-- The Hermitian Pauli operator `W_(a,b) = i^{Σ_j a_j b_j} X^a Z^b` (§3.2, printed p. 9),
with integer lifts of the bits in the exponent.  As a matrix in the computational basis,
`(X^a Z^b)_{x,y} = 1{x = y + a} (-1)^{b·y}`. -/
def W {n : ℕ} (u : Label n) : Op (Qubits n) := fun x y =>
  Complex.I ^ (∑ j, (u.1 j).val * (u.2 j).val) *
    (if ofQubits x = ofQubits y + u.1 then (1 : ℂ) else 0) *
    (-1 : ℂ) ^ (∑ j, (u.2 j).val * (ofQubits y j).val)

/-- The real Pauli expectation `tr(ρ W_u)` (real for Hermitian `ρ`). -/
def pauliExp {n : ℕ} (ρ : Op (Qubits n)) (u : Label n) : ℝ := (ρ * W u).trace.re

/-- The purity `tr(ρ²)`. -/
def purity {n : ℕ} (ρ : Op (Qubits n)) : ℝ := (ρ * ρ).trace.re

/-- A binary linear subspace `T ⊆ F₂^{2n}` is *isotropic* if the symplectic form vanishes on it
(§3.3); it may have any dimension `0 ≤ r ≤ n`. -/
def IsIsotropic {n : ℕ} (T : Submodule (ZMod 2) (Label n)) : Prop :=
  ∀ u ∈ T, ∀ v ∈ T, symp u v = 0

/-- A *full* (maximal) isotropic space: isotropic of dimension `n` (the published Lagrangian
predicate `StabTestMem.IsLagrangian`). -/
abbrev IsFull {n : ℕ} (T : Submodule (ZMod 2) (Label n)) : Prop := StabTestMem.IsLagrangian T

/-- The symplectic dual `T^⊥ = {v : ⟨v,t⟩ = 0 ∀ t ∈ T}` (§3.3, printed p. 10). -/
def perp {n : ℕ} (T : Submodule (ZMod 2) (Label n)) : Submodule (ZMod 2) (Label n) where
  carrier := {v | ∀ t ∈ T, symp v t = 0}
  zero_mem' := by
    intro t _
    simp [symp, CutRankSched.symp]
  add_mem' := by
    intro x y hx hy t ht
    have h1 := hx t ht
    have h2 := hy t ht
    simp only [symp, CutRankSched.symp] at h1 h2 ⊢
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]
    linear_combination h1 + h2
  smul_mem' := by
    intro c x hx t ht
    have h1 := hx t ht
    simp only [symp, CutRankSched.symp] at h1 ⊢
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul]
    linear_combination c * h1

/-- The affine filter (syndrome coset) `A_L = {m : ⟨m,t⟩ = Q(t) for all t ∈ L}`
(equation (50), printed p. 14).  It ignores the signs of any stabilizer generators. -/
def affineFilter {n : ℕ} (L : Submodule (ZMod 2) (Label n)) : Set (Label n) :=
  {m | ∀ t ∈ L, symp m t = Q t}

/-- The Hermitian generator `G_j = (-1)^{c_j} W_{b_j}`, for a list of labels `b` and signs `c`. -/
def generator {n r : ℕ} (b : Fin r → Label n) (c : Fin r → ZMod 2) (j : Fin r) :
    Op (Qubits n) :=
  (signZ (c j) : ℂ) • W (b j)

/-- The syndrome projector `Π_s = ∏_{j=1}^r (I + (-1)^{s_j} G_j)/2` (equation (30),
printed p. 10), for generators `G_j = (-1)^{c_j} W_{b_j}`; the product is taken in the
order `j = 1, …, r` (the factors commute when the labels are isotropic). -/
def syndromeProj {n r : ℕ} (b : Fin r → Label n) (c : Fin r → ZMod 2) (s : Fin r → ZMod 2) :
    Op (Qubits n) :=
  (List.ofFn fun j => (1 / 2 : ℂ) • (1 + (signZ (s j) : ℂ) • generator b c j)).prod

/-- The syndrome probability `p_s = tr(ρ Π_s)` (equation (31)). -/
def syndromeProb {n r : ℕ} (ρ : Op (Qubits n)) (b : Fin r → Label n) (c : Fin r → ZMod 2)
    (s : Fin r → ZMod 2) : ℝ :=
  (ρ * syndromeProj b c s).trace.re

/-- `b` is a basis of `T`: linearly independent labels spanning `T`. -/
def IsLabelBasis {n r : ℕ} (T : Submodule (ZMod 2) (Label n)) (b : Fin r → Label n) : Prop :=
  LinearIndependent (ZMod 2) b ∧ Submodule.span (ZMod 2) (Set.range b) = T

end BatchStabilizer.Learning


