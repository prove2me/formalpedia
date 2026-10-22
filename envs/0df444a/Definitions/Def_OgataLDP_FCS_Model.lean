-- Prove2me | Definitions.Def_OgataLDP_FCS_Model
-- name    : OgataLDP_FCS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:58.995545+00:00
-- url     : https://prove2.me/theorems/a5ce0858-472d-4287-a197-962445446d98
-- title:
--   The finite-chain interaction, finitely correlated state, spectral law, and large-deviation bounds
-- statement:
--   This module fixes the finite-dimensional model used throughout the mission. At each site the algebra is a full complex matrix algebra. An interaction assigns a Hermitian operator to each finite site set, is invariant under translation, and vanishes beyond a finite range. The Hamiltonian on sites $1,\ldots,n$ sums every term supported inside that interval, including the scalar empty-set term.
--
--   A finitely correlated state is specified by a finite-dimensional auxiliary matrix algebra, a unital completely positive transfer map $\mathcal E$, and a faithful stationary density matrix $\hat\rho$. Its local state $\omega_n$ is obtained by iterating $\mathcal E$ from the last site to the first. The same iteration over $l$ sites, $\mathcal E^{(l)}(A_1\otimes\cdots\otimes A_l\otimes b)=\mathcal E(A_1\otimes\mathcal E(A_2\otimes\cdots\mathcal E(A_l\otimes b)))$, is the $l$-th iterate of $\mathcal E$, and $(\mathcal B,\mathcal E^{(l)},\rho)$ is the $l$-block data on the site algebra $M_d(\mathbb C)^{\otimes l}$. For a Hermitian observable $H$, its spectral distribution assigns to each eigenvalue the state weight of the corresponding spectral projection. Thus the law $\mu_{n,\Phi}$ is the spectral distribution of $H_\Phi([1,n])/n$ under $\omega_n$.
--
--   A **good rate function** $I:\mathbb R\to[0,\infty]$ is lower semicontinuous and has compact finite sublevel sets. The full large-deviation principle requires, for every closed $C$ and open $O$,
--
--   $$\limsup_{n\to\infty}\frac1n\log\mu_{n,\Phi}(C)\le-\inf_{x\in C}I(x),\qquad
--   \liminf_{n\to\infty}\frac1n\log\mu_{n,\Phi}(O)\ge-\inf_{x\in O}I(x).$$
--
--   These definitions supply one common meaning for the goal and every milestone.
--
--   **Formalization Note** The one-site basis is an arbitrary finite nonempty type. The auxiliary algebra is represented as a full matrix algebra, which gives the same finitely correlated local states as a finite-dimensional $C^*$-algebra after a faithful matrix representation and conditional expectation. Site 1 has index 0. The interaction is stored by terms anchored at their least site. The state uses the primal form of the paper's dual-map recursion. Probabilities use an extended logarithm, with $\log 0=-\infty$. The value of the spectral-law function at non-Hermitian inputs is irrelevant to every stated use.
-- source:
--   Ogata, arXiv:0803.0113v1, pp. 2–4, definitions of interaction, Hamiltonian, spectral distribution, LDP, and finitely correlated state

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexOrder Matrix ENNReal NNReal

namespace OgataLDP.FCS

/-- The algebra on sites `1, …, n`, with site 1 represented by index 0. -/
abbrev Chain (σ : Type*) (n : ℕ) := Matrix (Fin n → σ) (Fin n → σ) ℂ

/-- Embed an operator on selected sites into a finite spin chain. -/
def embedVia {σ α : Type*} [Fintype σ] [Fintype α] [DecidableEq σ]
    {n : ℕ} (w : α ↪ Fin n) (A : Matrix (α → σ) (α → σ) ℂ) : Chain σ n := by
  classical
  exact Matrix.of fun x y =>
    if ∀ i : Fin n, i ∉ Set.range w → x i = y i then A (x ∘ w) (y ∘ w) else 0

/-- A finite-range translation-invariant interaction, recorded by the nonempty subsets
of `{0,…,r}` anchored at their least site, and by the scalar empty-set term. -/
structure Interaction (σ : Type*) [Fintype σ] where
  r : ℕ
  empty : ℝ
  term : (X : Finset (Fin (r + 1))) → Matrix (X → σ) (X → σ) ℂ
  herm : ∀ X, (term X).IsHermitian
  anchored : ∀ X, (0 : Fin (r + 1)) ∉ X → term X = 0

/-- Place the anchored term `X` at site `j` when its translate fits in the chain. -/
def shiftEmb {r n : ℕ} (j : Fin n) (X : Finset (Fin (r + 1)))
    (h : ∀ i ∈ X, (j : ℕ) + (i : ℕ) < n) : X ↪ Fin n where
  toFun i := ⟨(j : ℕ) + (i : ℕ), h i i.property⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hab)

/-- The paper's `H_Φ([1,n]) = ∑_{I ⊆ [1,n]} Φ(I)`. -/
def Interaction.hamiltonian {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Phi : Interaction σ) (n : ℕ) : Chain σ n := by
  classical
  exact (Phi.empty : ℂ) • 1 +
    ∑ j : Fin n, ∑ X : Finset (Fin (Phi.r + 1)),
      if h : ∀ i ∈ X, (j : ℕ) + (i : ℕ) < n then
        embedVia (shiftEmb j X h) (Phi.term X)
      else 0

/-- The site-first transfer map and the density of the boundary state. -/
structure FCSData (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) where
  E : Matrix (σ × Fin k) (σ × Fin k) ℂ →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ
  rho : Matrix (Fin k) (Fin k) ℂ

/-- `ρ(b) = Tr(ρ̂ b)`. -/
def FCSData.rhoState {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ}
    (F : FCSData σ k) (b : Matrix (Fin k) (Fin k) ℂ) : ℝ :=
  (F.rho * b).trace.re

/-- `Ê₁(b) = ℰ(1 ⊗ b)`. -/
def FCSData.Ehat1 {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ}
    (F : FCSData σ k) : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ) :=
  F.E.comp (Matrix.kroneckerBilinear (1 : Matrix σ σ ℂ))

/-- Unital complete positivity, a faithful normalized boundary state, and stationarity.
The final equality is the primal form of `Tr_{M_d}(ℰ*(ρ̂)) = ρ̂`. -/
def FCSData.IsValid {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ}
    (F : FCSData σ k) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive F.E ∧ F.E 1 = 1 ∧
  F.rho.PosDef ∧ F.rho.trace = 1 ∧
  ∀ b, (F.rho * F.Ehat1 b).trace = (F.rho * b).trace

/-- The iterated transfer map on `n` sites. Site 1 is the outermost application of `ℰ`. -/
def FCSData.iter {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ}
    (F : FCSData σ k) : (n : ℕ) →
    Matrix ((Fin n → σ) × Fin k) ((Fin n → σ) × Fin k) ℂ →
      Matrix (Fin k) (Fin k) ℂ
  | 0, X => Matrix.of fun b c => X ((Fin.elim0, b)) ((Fin.elim0, c))
  | n + 1, X => F.E (Matrix.of fun ab a'b' =>
      F.iter n (Matrix.of fun (vc v'c' : (Fin n → σ) × Fin k) =>
        X ((Fin.cons ab.1 vc.1, vc.2)) ((Fin.cons a'b'.1 v'c'.1, v'c'.2))) ab.2 a'b'.2)

/-- The iterated transfer map `ℰ_n` bundled as a `ℂ`-linear map. -/
def FCSData.iterLin {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ}
    (F : FCSData σ k) (n : ℕ) :
    Matrix ((Fin n → σ) × Fin k) ((Fin n → σ) × Fin k) ℂ →ₗ[ℂ]
      Matrix (Fin k) (Fin k) ℂ where
  toFun := F.iter n
  map_add' := by
    induction n with
    | zero => intro X Y; rfl
    | succ n ih =>
      intro X Y
      simp only [FCSData.iter]
      rw [← map_add]
      congr 1
      ext p q
      have hpq : (Matrix.of fun (vc v'c' : (Fin n → σ) × Fin k) =>
          (X + Y) (Fin.cons p.1 vc.1, vc.2) (Fin.cons q.1 v'c'.1, v'c'.2)) =
          (Matrix.of fun (vc v'c' : (Fin n → σ) × Fin k) => X (Fin.cons p.1 vc.1, vc.2) (Fin.cons q.1 v'c'.1, v'c'.2)) +
          (Matrix.of fun (vc v'c' : (Fin n → σ) × Fin k) => Y (Fin.cons p.1 vc.1, vc.2) (Fin.cons q.1 v'c'.1, v'c'.2)) := by
        ext; rfl
      change F.iter n _ p.2 q.2 = F.iter n _ p.2 q.2 + F.iter n _ p.2 q.2
      rw [hpq, ih]
      rfl
  map_smul' := by
    induction n with
    | zero => intro c X; rfl
    | succ n ih =>
      intro c X
      simp only [FCSData.iter, RingHom.id_apply]
      rw [← map_smul]
      congr 1
      ext p q
      have hpq : (Matrix.of fun (vc v'c' : (Fin n → σ) × Fin k) =>
          (c • X) (Fin.cons p.1 vc.1, vc.2) (Fin.cons q.1 v'c'.1, v'c'.2)) =
          c • (Matrix.of fun (vc v'c' : (Fin n → σ) × Fin k) => X (Fin.cons p.1 vc.1, vc.2) (Fin.cons q.1 v'c'.1, v'c'.2)) := by
        ext; rfl
      change F.iter n _ p.2 q.2 = c • F.iter n _ p.2 q.2
      rw [hpq, ih]
      rfl

/-- The `l`-block data `(ℬ, ℰ^{(l)}, ρ)` on the site algebra `M_d(ℂ)^{⊗ l}`, where
`ℰ^{(l)}(A_1 ⊗ ⋯ ⊗ A_l ⊗ b) = ℰ(A_1 ⊗ ℰ(A_2 ⊗ ⋯ ℰ(A_l ⊗ b)))` is the `l`-th iterate of `ℰ`. -/
def FCSData.block {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ}
    (F : FCSData σ k) (l : ℕ) : FCSData (Fin l → σ) k where
  E := F.iterLin l
  rho := F.rho

/-- The local restriction `ω_n(A) = ρ(ℰ_n(A ⊗ 1))`. -/
def FCSData.localState {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ}
    (F : FCSData σ k) (n : ℕ) (A : Chain σ n) : ℂ :=
  (F.rho * F.iter n (Matrix.kronecker A 1)).trace

/-- Spectral distribution of a Hermitian finite-dimensional observable in a state.
The branch for non-Hermitian input is irrelevant for an interaction Hamiltonian. -/
def specDist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (omega : Matrix ι ι ℂ → ℂ) (H : Matrix ι ι ℂ) : Measure ℝ :=
  if h : H.IsHermitian then
    ∑ i : ι,
      ENNReal.ofReal ((omega (Matrix.vecMulVec
        (fun j => (h.eigenvectorBasis i) j)
        (fun j => star ((h.eigenvectorBasis i) j)))).re) •
      Measure.dirac (h.eigenvalues i)
  else 0

/-- The paper's lower-semicontinuous good rate functions. -/
def IsGoodRate (I : ℝ → ℝ≥0∞) : Prop :=
  LowerSemicontinuous I ∧ ∀ a : ℝ≥0, IsCompact {x | I x ≤ a}

/-- The upper bound for every closed set, with `log 0 = -∞`. -/
def LDPUpper (mu : ℕ → Measure ℝ) (I : ℝ → ℝ≥0∞) : Prop :=
  ∀ C : Set ℝ, IsClosed C →
    limsup (fun n : ℕ => (1 / (n : EReal)) * ENNReal.log (mu n C)) atTop ≤
      -((⨅ x ∈ C, I x : ℝ≥0∞) : EReal)

/-- The lower bound for every open set, with `log 0 = -∞`. -/
def LDPLower (mu : ℕ → Measure ℝ) (I : ℝ → ℝ≥0∞) : Prop :=
  ∀ O : Set ℝ, IsOpen O →
    -((⨅ x ∈ O, I x : ℝ≥0∞) : EReal) ≤
      liminf (fun n : ℕ => (1 / (n : EReal)) * ENNReal.log (mu n O)) atTop

def SatisfiesLDP (mu : ℕ → Measure ℝ) (I : ℝ → ℝ≥0∞) : Prop :=
  LDPUpper mu I ∧ LDPLower mu I

end OgataLDP.FCS


