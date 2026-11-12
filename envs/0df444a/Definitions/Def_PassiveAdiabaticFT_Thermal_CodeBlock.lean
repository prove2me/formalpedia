-- Prove2me | Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock
-- name    : PassiveAdiabaticFT_Thermal_CodeBlock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:17.633562+00:00
-- url     : https://prove2.me/theorems/57a9de6e-6616-473d-93d2-40e7fed60c16
-- title:
--   One code block: stabilizer code, Pauli decoder, $W$, Dec, thermal encoding, barrier and dangerous syndromes
-- statement:
--   Let $C$ be a stabilizer code on $b$ qubits with $k\ge1$ logical qubits, given by a generating set $(P_a)_{a\in A}$ of pairwise commuting Hermitian Pauli strings, together with an encoder isometry $V:(\mathbb C^2)^{\otimes k}\to(\mathbb C^2)^{\otimes b}$ onto the code space. For $s\in\{0,1\}^A$,
--   $$\Pi_s=\prod_{a\in A}\frac{I+(-1)^{s_a}P_a}{2}\quad(1.1),\qquad \Omega=\{s:\Pi_s\ne0\},$$
--   and $V V^\dagger=\Pi_0$. A **Pauli decoder** is a choice of Pauli corrections $R_s$, $s\in\Omega$, with $R_sP_aR_s^\dagger=(-1)^{s_a}P_a$ (1.2) and $R_0=I$. From these data:
--
--   1. $W(|\psi\rangle\otimes|s\rangle)=R_s^\dagger V|\psi\rangle$ (1.4); $\mathrm{Dec}[\rho]=\sum_{s\in\Omega}V^\dagger R_s\Pi_s\rho\Pi_sR_s^\dagger V$ (1.3); the dressed operator $\hat O=W(O\otimes I)W^\dagger$ (1.5).
--   2. $H_0=J\sum_a(I-P_a)$ (1.6); $E[s]=2J|s|$ with $|s|$ the number of violated checks (1.7); $Z(\beta)=\operatorname{Tr}e^{-\beta H_0}$ and $Z_{\rm syn}(\beta)=\sum_{s\in\Omega}e^{-\beta E[s]}$ (1.8); $\pi_\beta(s)=e^{-\beta E[s]}/Z_{\rm syn}(\beta)$ (1.9); the thermal encoding $\mathrm{Enc}_{\beta'}(\rho)=W\big(\rho\otimes\sum_{s}\pi_{\beta'}(s)|s\rangle\langle s|\big)W^\dagger$ (1.11) and the code-space encoding $V\rho V^\dagger$.
--   3. The syndrome $s(Q)$ of a Pauli $Q$, $P_aQ=(-1)^{s(Q)_a}QP_a$ (1.26), and the **logical energy barrier** (Definition 1.3): for single-qubit Paulis $A_1,\dots,A_\ell$ with $A^{(j)}=A_j\cdots A_1$,
--   $$\Delta_n=\min_{A^{(\ell)}\text{ nontrivial logical}}\ \max_{0\le j\le\ell}E[s(A^{(j)})],$$
--   where a nontrivial logical Pauli commutes with every $P_a$ and is not a stabilizer up to phase.
--   4. For a single-qubit Pauli $F_\alpha$: $e_\alpha$ with $P_aF_\alpha=(-1)^{(e_\alpha)_a}F_\alpha P_a$ (2.2), $f_\alpha(s)=s\oplus e_\alpha$, the block $G_s^{(\alpha)}=V^\dagger R_{f_\alpha(s)}F_\alpha R_s^\dagger V$ (2.3), the **dangerous syndromes** $D_\alpha=\{s\in\Omega:G_s^{(\alpha)}\not\propto I\}$ (2.5) and $\mathcal B_{\rm dec}=\bigcup_\alpha D_\alpha$ (2.6); $\delta_n=\max_{\alpha,s}|E[f_\alpha(s)]-E[s]|$ (2.16); $\Omega_{>E}=\{s\in\Omega:E[s]>E\}$ (2.15).
--   5. Condition 1 of Definition 1.1 for $B\subseteq\Omega$: $[\hat O,P](I-\Pi_B)=0$ for every logical operator $O$ and single-qubit Pauli $P$, with $\Pi_B=\sum_{s\in B}\Pi_s$. Qubit degree and check weight count the checks acting nontrivially on a qubit and the qubits a check acts on.
--
--   These are the objects of §1.1 and §2, used by every statement of the mission.
--
--   **Formalization Note** The generators need not be independent (as for quantum Tanner codes); existence of $V$ with $V^\dagger V=I$ and $VV^\dagger=\Pi_0$ forces $\Pi_0\ne0$ and $\operatorname{rank}\Pi_0=2^k$. The barrier is computed in violated checks as a natural-number infimum (the set is nonempty when $k\ge1$) and multiplied by $2J$; $\delta_n$ likewise. $f_\alpha$ on the register $\Omega$ has a fallback branch that is never taken, since $f_\alpha$ maps $\Omega$ into $\Omega$ (Lemma 2.2).
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, §1.1 eqs. (1.1)–(1.11) (pp. 3–5), Definition 1.1 condition 1 (p. 7), (1.26) and Definition 1.3 (1.27) (pp. 7–8), §2.1 (2.2)–(2.6), Definition 2.3 (pp. 12–13), (2.15)–(2.16) (p. 15)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_Operators

/-!
# One code block: stabilizer code, Pauli decoder, thermal encoding, barrier, dangerous syndromes

Arsalan Motamedi, Peter Love, *Fault Tolerant Adiabatic Quantum Computation from Passive Error
Correcting Codes*, STOC 2027 submission #1144 (October 2026): §1.1 eqs. (1.1)–(1.11) (pp. 3–5),
Definition 1.1 condition 1 (p. 7), (1.26)–(1.27) and Definition 1.3 (pp. 7–8),
§2.1 eqs. (2.2)–(2.6) and Definition 2.3 (pp. 12–13), (2.15)–(2.16) (p. 15).
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- The sign `(-1)^z` of a bit `z ∈ ZMod 2`. -/
def sgn (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

/-- The syndrome projector (1.1): `Π_s = ∏_{a} (I + (−1)^{s_a} P_a)/2` for generators
`P : Fin m → Op Q` (an ordered product; the generators of a stabilizer code commute). -/
def synProj {Q : Type} [Fintype Q] [DecidableEq Q] {m : ℕ} (P : Fin m → Op Q)
    (s : Fin m → ZMod 2) : Op Q :=
  (List.ofFn fun a => ((1 / 2 : ℂ)) • (1 + sgn (s a) • P a)).prod

/-- An `[[b, k]]` stabilizer code (§1.1) with `k ≥ 1`, given by a generating set
`P_0, …, P_{m-1}` of pairwise commuting Hermitian Pauli strings (not required to be independent),
together with an encoder: an isometry `V : (ℂ²)^{⊗k} → (ℂ²)^{⊗b}` onto the code space
`Π_0` (the joint `+1` eigenspace). That `V` exists with `V V† = Π_0` forces `Π_0 ≠ 0`, i.e.
`−I` is not in the stabilizer group, and `rank Π_0 = 2^k`. -/
structure StabCode (b : ℕ) where
  m : ℕ
  P : Fin m → Op (Fin b)
  P_pauli : ∀ a, IsPauli (P a)
  P_herm : ∀ a, (P a)ᴴ = P a
  P_comm : ∀ a a', P a * P a' = P a' * P a
  k : ℕ
  k_pos : 1 ≤ k
  V : Matrix (Fin b → Fin 2) (Fin k → Fin 2) ℂ
  V_isom : Vᴴ * V = 1
  V_range : V * Vᴴ = synProj P 0

/-- The single-qubit Pauli `F_α` on a block of `b` qubits, `α = (qubit, Pauli type)`. -/
def Fα {b : ℕ} (α : Fin b × Fin 3) : Op (Fin b) := singlePauli α.1 α.2

namespace StabCode

variable {b : ℕ} (C : StabCode b)

open Classical in
/-- The acceptable syndromes `Ω = {s : Π_s ≠ 0}` (p. 4). -/
def Omega : Finset (Fin C.m → ZMod 2) :=
  Finset.univ.filter fun s => synProj C.P s ≠ 0

/-- The syndrome register: the acceptable syndromes as a type. -/
abbrev Om : Type := {s : Fin C.m → ZMod 2 // s ∈ C.Omega}

/-- The number `|s|` of violated checks of a syndrome. -/
def weight (s : Fin C.m → ZMod 2) : ℕ := (Finset.univ.filter fun a => s a ≠ 0).card

/-- The energy `E[s] = 2J|s|` (1.7). -/
def energy (J : ℝ) (s : Fin C.m → ZMod 2) : ℝ := 2 * J * C.weight s

/-- The code Hamiltonian (1.6): `H_0 = J Σ_a (I − P_a)`. -/
def H0 (J : ℝ) : Op (Fin b) := (J : ℂ) • ∑ a, (1 - C.P a)

/-- The partition function (1.8): `Z(β) = Tr e^{−βH_0}`. -/
def Z (J β : ℝ) : ℝ := (Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • C.H0 J))).re

/-- The syndrome partition function (1.8): `Z_syn(β) = Σ_{s ∈ Ω} e^{−βE[s]}`. -/
def Zsyn (J β : ℝ) : ℝ := ∑ s ∈ C.Omega, Real.exp (-(β * C.energy J s))

/-- The syndrome Gibbs distribution (1.9): `π_β(s) = e^{−βE[s]}/Z_syn(β)`. -/
def gibbs (J β : ℝ) (s : Fin C.m → ZMod 2) : ℝ :=
  Real.exp (-(β * C.energy J s)) / C.Zsyn J β

/-- The Gibbs weight of a set of syndromes, `π_β(S) = Σ_{s ∈ S} π_β(s)`. -/
def gibbsSet (J β : ℝ) (S : Finset (Fin C.m → ZMod 2)) : ℝ := ∑ s ∈ S, C.gibbs J β s

open Classical in
/-- The projector `Π_S = Σ_{s ∈ S} Π_s` onto a set of syndromes. -/
def projSet (S : Finset (Fin C.m → ZMod 2)) : Op (Fin b) := ∑ s ∈ S, synProj C.P s

/-- The syndrome `s(Q)` of a Pauli `Q` (1.26): `P_a Q = (−1)^{s(Q)_a} Q P_a`. -/
def synOf (Qop : Op (Fin b)) : Fin C.m → ZMod 2 :=
  fun a => if C.P a * Qop = Qop * C.P a then 0 else 1

/-- `Qop` is a stabilizer up to phase: a scalar multiple of a product of generators. -/
def IsStabUpToPhase (Qop : Op (Fin b)) : Prop :=
  ∃ c : ℂ, ∃ S : Finset (Fin C.m), Qop = c • ((S.sort (· ≤ ·)).map C.P).prod

/-- `Qop` acts as a nontrivial logical Pauli: it commutes with every generator and is not a
stabilizer up to phase. -/
def IsNontrivialLogical (Qop : Op (Fin b)) : Prop :=
  (∀ a, C.P a * Qop = Qop * C.P a) ∧ ¬ C.IsStabUpToPhase Qop

/-- For a sequence `A_1, …, A_ℓ` of single-qubit Paulis (a list of (qubit, Pauli type)), the
prefix product `A^{(j)} = A_j ⋯ A_1` (`A^{(0)} = I`). -/
def pathPrefix (l : List (Fin b × Fin 3)) (j : ℕ) : Op (Fin b) :=
  ((l.take j).map fun p => singlePauli p.1 p.2).reverse.prod

/-- The height of a path in violated checks, `max_{0 ≤ j ≤ ℓ} |s(A^{(j)})|`. -/
def pathHeight (l : List (Fin b × Fin 3)) : ℕ :=
  (Finset.range (l.length + 1)).sup fun j => C.weight (C.synOf (pathPrefix l j))

/-- The logical energy barrier of Definition 1.3 in violated checks: the least height of a
single-qubit Pauli path whose product `A^{(ℓ)}` acts as a nontrivial logical Pauli. (The set is
nonempty for `k ≥ 1`; the `ℕ`-infimum of the empty set would be `0`.) -/
def barrierCount : ℕ :=
  sInf {h | ∃ l : List (Fin b × Fin 3),
    C.IsNontrivialLogical (pathPrefix l l.length) ∧ C.pathHeight l = h}

/-- The logical energy barrier (1.27): `Δ_n = 2J · barrierCount`. -/
def barrier (J : ℝ) : ℝ := 2 * J * C.barrierCount

/-- The syndrome flip `e_α` of (2.2): `P_a F_α = (−1)^{(e_α)_a} F_α P_a`. -/
def e (α : Fin b × Fin 3) : Fin C.m → ZMod 2 := C.synOf (Fα α)

/-- The syndrome map `f_α(s) = s ⊕ e_α` (Lemma 2.2). -/
def f (α : Fin b × Fin 3) (s : Fin C.m → ZMod 2) : Fin C.m → ZMod 2 := s + C.e α

/-- `f_α` on the syndrome register (it maps `Ω` to `Ω`, Lemma 2.2; the fallback branch is never
taken). -/
def fOm (α : Fin b × Fin 3) (s : C.Om) : C.Om :=
  if h : C.f α s.1 ∈ C.Omega then ⟨C.f α s.1, h⟩ else s

open Classical in
/-- The maximal energy change of a single-qubit Pauli (2.16), in violated checks:
`max_{α, s ∈ Ω} | |f_α(s)| − |s| |`. -/
def deltaCount : ℕ :=
  (Finset.univ ×ˢ C.Omega).sup fun p =>
    Int.natAbs ((C.weight (C.f p.1 p.2) : ℤ) - C.weight p.2)

/-- `δ_n = max_{α,s} |E[f_α(s)] − E[s]|` (2.16). -/
def delta (J : ℝ) : ℝ := 2 * J * C.deltaCount

open Classical in
/-- `Ω_{>E} = {s ∈ Ω : E[s] > E}` (2.15). -/
def OmegaGt (J E : ℝ) : Finset (Fin C.m → ZMod 2) :=
  C.Omega.filter fun s => E < C.energy J s

/-- Qubit `q` belongs to check `a`: `P_a` acts nontrivially on `q`, i.e. fails to commute with
some single-qubit Pauli on `q`. -/
def InCheck (q : Fin b) (a : Fin C.m) : Prop :=
  ∃ c : Fin 3, C.P a * singlePauli q c ≠ singlePauli q c * C.P a

open Classical in
/-- The number of checks qubit `q` belongs to. -/
def qubitDegree (q : Fin b) : ℕ := (Finset.univ.filter fun a => C.InCheck q a).card

open Classical in
/-- The weight of check `a`: the number of qubits it acts on nontrivially. -/
def checkWeight (a : Fin C.m) : ℕ := (Finset.univ.filter fun q => C.InCheck q a).card

/-- The code-space encoding `Enc(ρ) = V ρ V†`. -/
def encCode (ρ : Op (Fin C.k)) : Op (Fin b) := C.V * ρ * C.Vᴴ

end StabCode

/-- A Pauli decoder for `C` (§1.1): Pauli corrections `R_s`, `s ∈ Ω`, with
`R_s P_a R_s† = (−1)^{s_a} P_a` (1.2) and `R_0 = I`. Values off `Ω` are never used. -/
structure PauliDecoder {b : ℕ} (C : StabCode b) where
  R : (Fin C.m → ZMod 2) → Op (Fin b)
  R_pauli : ∀ s ∈ C.Omega, IsPauli (R s)
  R_syn : ∀ s ∈ C.Omega, ∀ a, R s * C.P a * (R s)ᴴ = sgn (s a) • C.P a
  R_zero : R 0 = 1

namespace PauliDecoder

variable {b : ℕ} {C : StabCode b} (D : PauliDecoder C)

/-- The unitary `W` of (1.4): `W(|ψ⟩ ⊗ |s⟩) = R_s† V |ψ⟩` for `s ∈ Ω`. -/
def W : Matrix (Fin b → Fin 2) ((Fin C.k → Fin 2) × C.Om) ℂ :=
  fun x p => ((D.R p.2.1)ᴴ * C.V) x p.1

/-- The decoder channel (1.3): `Dec[ρ] = Σ_{s ∈ Ω} V† R_s Π_s ρ Π_s R_s† V`. -/
def dec (ρ : Op (Fin b)) : Op (Fin C.k) :=
  ∑ s ∈ C.Omega, C.Vᴴ * D.R s * synProj C.P s * ρ * synProj C.P s * (D.R s)ᴴ * C.V

/-- The dressed logical operator (1.5): `Ô = W (O ⊗ I) W†`. -/
def dressed (O : Op (Fin C.k)) : Op (Fin b) :=
  D.W * Matrix.kroneckerMap (· * ·) O (1 : Matrix C.Om C.Om ℂ) * D.Wᴴ

/-- The thermal encoding (1.11)/(1.31):
`Enc_{β'}(ρ) = W (ρ ⊗ Σ_{s ∈ Ω} π_{β'}(s) |s⟩⟨s|) W†`. -/
def encTh (J β' : ℝ) (ρ : Op (Fin C.k)) : Op (Fin b) :=
  D.W * Matrix.kroneckerMap (· * ·) ρ
    (Matrix.diagonal fun s : C.Om => ((C.gibbs J β' s.1 : ℝ) : ℂ)) * D.Wᴴ

/-- The logical block (2.3): `G_s^{(α)} = V† R_{f_α(s)} F_α R_s† V`, the block of `W† F_α W`
from syndrome `s` to `f_α(s)`. -/
def G (α : Fin b × Fin 3) (s : Fin C.m → ZMod 2) : Op (Fin C.k) :=
  C.Vᴴ * D.R (C.f α s) * Fα α * (D.R s)ᴴ * C.V

open Classical in
/-- The dangerous syndromes for `F_α` (Definition 2.3, (2.5)): `D_α = {s ∈ Ω : G_s^{(α)} ∉ ℂ·I}`. -/
def Dset (α : Fin b × Fin 3) : Finset (Fin C.m → ZMod 2) :=
  C.Omega.filter fun s => ¬ ∃ c : ℂ, D.G α s = c • (1 : Op (Fin C.k))

open Classical in
/-- The decoder-bad set (2.6): `B_dec = ⋃_α D_α`, over all `3b` single-qubit Paulis. -/
def Bdec : Finset (Fin C.m → ZMod 2) := Finset.univ.biUnion D.Dset

/-- Condition 1 of Definition 1.1 for a set `B ⊆ Ω`: `[Ô, P](I − Π_B) = 0` for every logical
operator `O` and every single-qubit Pauli `P`. -/
def BadSetCondition (B : Finset (Fin C.m → ZMod 2)) : Prop :=
  B ⊆ C.Omega ∧ ∀ (O : Op (Fin C.k)) (α : Fin b × Fin 3),
    (D.dressed O * Fα α - Fα α * D.dressed O) * (1 - C.projSet B) = 0

end PauliDecoder

end PassiveAdiabaticFT.Thermal


