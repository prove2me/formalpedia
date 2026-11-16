-- Prove2me | Definitions.Def_TightQLB_Supplement_Level
-- name    : TightQLB_Supplement_Level
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:19:14.974797+00:00
-- url     : https://prove2.me/theorems/701e3ee6-200b-413e-8501-5273bf865548
-- title:
--   Vector-valued polynomials $P_{\le d}(V)$, patterns, blocks, the level and the progress measure $\lambda$, the score form $\langle F,XF\rangle$
-- statement:
--   Let $V$ be a finite-dimensional space. $P_{\le d}(V)$ is the space of functions $F$ from the unit sphere of $\mathbb C^N$ to $V$ that are polynomials of total degree at most $d$ in the $2N$ variables $\alpha_x,\bar\alpha_x$, with
--
--   $$
--   \langle F,G\rangle=\mathbb E_\phi\langle F(\phi),G(\phi)\rangle_V ,
--   $$
--
--   $\mathbb E_\phi$ the Haar expectation. A **pattern** is $\gamma\in\mathbb Z^N$, with phase monomial $u_\gamma=\prod_{\gamma_i>0}\alpha_i^{\gamma_i}\prod_{\gamma_i<0}\bar\alpha_i^{-\gamma_i}$ and Dirichlet parameters $a(\gamma)=(1+|\gamma_1|,\dots,1+|\gamma_N|)$. A **block** is $u_\gamma R^{a(\gamma)}_r\otimes V$, where the polynomial factor is evaluated at $p=(|\alpha_x|^2)_x$; its **level** is $\mathrm{rep}(\gamma)+r$ with $\mathrm{rep}(\gamma)=\sum_i\max(|\gamma_i|-1,0)$. With $P_k$ the orthogonal projection onto the closed span of the blocks of level $k$, the **progress measure** is
--
--   $$
--   \lambda(F)=\Big(\sum_k k\,\|P_kF\|^2\Big)^{1/2}.
--   $$
--
--   For orthogonal projections $\{\Pi_z\}$ on $V$ summing to $I$, the score operator $X=\sum_zNp_z\Pi_z$ has quadratic form $\langle F,XF\rangle=N\sum_z\mathbb E_\phi[p_z\|\Pi_zF(\phi)\|^2]$, which is the expected score when $F$ is a final state.
--
--   The progress measure vanishes for honest sampling, controls the excess score (Theorem 5.13) and grows slowly under queries (Theorem 5.21).
--
--   **Formalization Note** A function of $\phi$ is `EuclideanSpace ℂ (Qubits n) → V → ℂ`; only its values on unit vectors matter. $\|P_kF\|$ is the supremum of $|\langle G,F\rangle|$ over $G$ in the span of the level-$k$ blocks with $\|G\|\le1$; since the blocks are pairwise orthogonal (Lemma 5.2), this is also the projection of $P_{\le d}(V)$ onto its level-$k$ blocks, so $\lambda$ does not depend on $d$. The sum over $k$ is a `tsum`; for a polynomial only finitely many terms are nonzero.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §5.1, Lemma 5.2, Definition 5.3, Eq. (41), pp. 30–33 (PDF pp. 33–36)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Haar
import Definitions.Def_TightQLB_Supplement_Dirichlet
open QAlgorithms MeasureTheory
open scoped Matrix

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# Vector-valued polynomials on the sphere, patterns, blocks, the level and the progress measure

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §5.1, pp.30–33
(PDF pp.33–36): the spaces `P_{≤d}(V)`, patterns and phase monomials, Lemma 5.2 (blocks),
Definition 5.3 (level), and the score operator `X` of (41).

"Let `P_{≤d}(V)` be the space of functions `F` from the unit sphere of `C^N` to `V` that are
polynomials of total degree at most `d` in the `2N` variables `α_x, ᾱ_x`. We use the inner product
and norm `⟨F, G⟩ = E_ϕ⟨F(ϕ), G(ϕ)⟩_V`." A pattern is `γ ∈ Z^N`, with phase monomial
`u_γ = Π_{γ_i>0} α_i^{γ_i} Π_{γ_i<0} ᾱ_i^{−γ_i}`, Dirichlet parameters
`a(γ) = (1 + |γ₁|, …, 1 + |γ_N|)`. The blocks are `u_γ R^{a(γ)}_r ⊗ V` (38). "The level of the
block indexed by `(γ, r)` is `rep(γ) + r`", `rep(γ) = Σ_i max(|γ_i| − 1, 0)`. "Let `P_k` be the
orthogonal projection onto the sum of the blocks of level `k`, and let `C = Σ_k k P_k` be the level
operator. The progress measure of a polynomial `F` is `λ(F) = ‖C^{1/2}F‖ = (Σ_k k‖P_kF‖²)^{1/2}`."
"`⟨F, XF⟩ = N Σ_z E_ϕ[p_z ‖Π_z F(ϕ)‖²]`" (41).

**Formalization Note.**
* `V` is the coordinate space of a finite type `V`; an `V`-valued function of the oracle state is
  `Fn n V = EuclideanSpace ℂ (Qubits n) → V → ℂ`, and only its values on unit vectors matter
  (`E_ϕ` is the Haar law `haar n` on unit vectors).
* `IsPoly d F`: on every unit vector, each coordinate of `F` is the value of a polynomial of total
  degree at most `d` in the `2N` variables `α_x` (`Sum.inl x`) and `ᾱ_x` (`Sum.inr x`).
* `u_γ` is `phaseMono γ`; `R^{a(γ)}_r` is the published-in-this-chunk `InR (aOf γ) r`, evaluated at
  `p = (|α_x|²)_x` (`probVec`); a vector `v ∈ V` is a constant coefficient.
* `P_k` is the orthogonal projection onto the closed span of all blocks of level `k` (of every
  degree). For `F ∈ P_{≤d}(V)` this is the projection of (38) onto the level-`k` blocks of degree
  at most `d`, because the blocks are pairwise orthogonal (Lemma 5.2); so `λ` does not depend on
  `d`. `‖P_k F‖` is `levelNorm k F`, the supremum of `|⟨G, F⟩|` over `G` in the span with
  `‖G‖ ≤ 1` (the norm of the projection onto the closure of the span).
* `λ(F) = (Σ_k k‖P_kF‖²)^{1/2}` is `progress F`, with the sum a `tsum` over `k ∈ ℕ`; for a
  polynomial `F ∈ P_{≤d}(V)` only the finitely many `k ≤ d` contribute.
* `⟨F, XF⟩` is `scoreForm Π F` for orthogonal projections `{Π_z}` on `V`.
-/

/-- Functions of the oracle state `ϕ` with values in the coordinate space of `V`. -/
abbrev Fn (n : ℕ) (V : Type) := EuclideanSpace ℂ (Qubits n) → V → ℂ

variable {n : ℕ} {V : Type} [Fintype V]

/-- `⟨F, G⟩ = E_ϕ ⟨F(ϕ), G(ϕ)⟩_V` (§5.1, p.30, PDF p.33), conjugate-linear in `F`. -/
noncomputable def hip (F G : Fn n V) : ℂ :=
  ∫ ϕ, ∑ w, star (F ϕ w) * G ϕ w ∂(haar n)

/-- `‖F‖² = E_ϕ ‖F(ϕ)‖²_V`. -/
noncomputable def hnormSq (F : Fn n V) : ℝ :=
  (hip F F).re

/-- `F ∈ P_{≤d}(V)`: on the unit sphere, every coordinate of `F` is a polynomial of total degree at
most `d` in `α_x` (`Sum.inl x`) and `ᾱ_x` (`Sum.inr x`). -/
def IsPoly (d : ℕ) (F : Fn n V) : Prop :=
  ∃ P : V → MvPolynomial (Qubits n ⊕ Qubits n) ℂ, (∀ w, (P w).totalDegree ≤ d) ∧
    ∀ ϕ : EuclideanSpace ℂ (Qubits n), ‖ϕ‖ = 1 → ∀ w,
      F ϕ w = MvPolynomial.eval (Sum.elim (fun x => ϕ x) (fun x => star (ϕ x))) (P w)

/-- The probability vector `p = (|α_x|²)_x` of `ϕ`, as a point of `R^N`. -/
noncomputable def probVec (ϕ : EuclideanSpace ℂ (Qubits n)) : EuclideanSpace ℝ (Qubits n) :=
  WithLp.toLp 2 (fun x => ‖ϕ x‖ ^ 2)

/-- §5.1, p.31 (PDF p.34): the phase monomial `u_γ = Π_{γ_i>0} α_i^{γ_i} Π_{γ_i<0} ᾱ_i^{−γ_i}` of a
pattern `γ ∈ Z^N`. -/
noncomputable def phaseMono (γ : Qubits n → ℤ) (ϕ : EuclideanSpace ℂ (Qubits n)) : ℂ :=
  ∏ x, if 0 ≤ γ x then ϕ x ^ (γ x).toNat else star (ϕ x) ^ (-γ x).toNat

/-- §5.1, p.31 (PDF p.34): the Dirichlet parameters `a(γ) = (1 + |γ₁|, …, 1 + |γ_N|)`. -/
noncomputable def aOf (γ : Qubits n → ℤ) : Qubits n → ℝ :=
  fun x => 1 + |((γ x : ℤ) : ℝ)|

/-- Definition 5.3, p.32 (PDF p.35): `rep(γ) = Σ_i max(|γ_i| − 1, 0)`. -/
def rep (γ : Qubits n → ℤ) : ℕ :=
  ∑ x, ((γ x).natAbs - 1)

/-- The element `u_γ(ϕ) h(p(ϕ)) v` of the block `u_γ R^{a(γ)}_r ⊗ V`. -/
noncomputable def blockFn (γ : Qubits n → ℤ) (h : MvPolynomial (Qubits n) ℂ) (v : V → ℂ) :
    Fn n V :=
  fun ϕ w => phaseMono γ ϕ * peval h (probVec ϕ) * v w

/-- The elements of the blocks of level `k` (Definition 5.3): `u_γ h v` with `h ∈ R^{a(γ)}_r`,
`v ∈ V`, and `rep(γ) + r = k`. -/
def levelSet (n : ℕ) (V : Type) [Fintype V] (k : ℕ) : Set (Fn n V) :=
  {G | ∃ (γ : Qubits n → ℤ) (r : ℕ) (h : MvPolynomial (Qubits n) ℂ) (v : V → ℂ),
    rep γ + r = k ∧ InR (aOf γ) r h ∧ G = blockFn γ h v}

/-- The span of the blocks of level `k`. -/
def levelSpan (n : ℕ) (V : Type) [Fintype V] (k : ℕ) : Submodule ℂ (Fn n V) :=
  Submodule.span ℂ (levelSet n V k)

/-- `‖P_k F‖`: the norm of the orthogonal projection of `F` onto the closed span of the level-`k`
blocks, i.e. the supremum of `|⟨G, F⟩|` over `G` in the span with `‖G‖ ≤ 1`. -/
noncomputable def levelNorm (k : ℕ) (F : Fn n V) : ℝ :=
  ⨆ G : {G : Fn n V // G ∈ levelSpan n V k ∧ hnormSq G ≤ 1}, ‖hip G.1 F‖

/-- Definition 5.3, p.32 (PDF p.35): the progress measure `λ(F) = (Σ_k k ‖P_k F‖²)^{1/2}`. -/
noncomputable def progress (F : Fn n V) : ℝ :=
  Real.sqrt (∑' k : ℕ, (k : ℝ) * levelNorm k F ^ 2)

/-- The `L²` norm `‖F‖ = (E_ϕ ‖F(ϕ)‖²)^{1/2}`. -/
noncomputable def hnorm (F : Fn n V) : ℝ :=
  Real.sqrt (hnormSq F)

/-- `{Π_z}_{z ∈ [N]}` is a family of orthogonal projections on `V` summing to `I`. -/
def IsProjFamily [DecidableEq V] (proj : Qubits n → Matrix V V ℂ) : Prop :=
  (∀ z, (proj z).IsHermitian) ∧ (∀ z, proj z * proj z = proj z) ∧ ∑ z, proj z = 1

/-- Eq. (41), p.33 (PDF p.36): the quadratic form of the score operator `X = Σ_z N p_z Π_z`,
`⟨F, XF⟩ = N Σ_z E_ϕ[p_z ‖Π_z F(ϕ)‖²]`. -/
noncomputable def scoreForm [DecidableEq V] (proj : Qubits n → Matrix V V ℂ) (F : Fn n V) : ℝ :=
  (2 : ℝ) ^ n * ∑ z, ∫ ϕ, pOf ϕ z * ∑ w, ‖(proj z *ᵥ F ϕ) w‖ ^ 2 ∂(haar n)

/-- An operator-valued function of `ϕ` applied pointwise: `(T F)(ϕ) = T(ϕ) F(ϕ)`. -/
def pointwise (T : EuclideanSpace ℂ (Qubits n) → Matrix V V ℂ) (F : Fn n V) : Fn n V :=
  fun ϕ => T ϕ *ᵥ F ϕ

/-- A vector-valued function of `ϕ` with values in `EuclideanSpace ℂ V`, as an element of `Fn n V`. -/
def ofVec (Ψ : EuclideanSpace ℂ (Qubits n) → EuclideanSpace ℂ V) : Fn n V :=
  fun ϕ w => Ψ ϕ w

end TightQLB.Supplement


