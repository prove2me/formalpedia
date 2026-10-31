-- Prove2me | Definitions.Def_DiazMultiplicity
-- name    : DiazMultiplicity
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-30T09:50:56.813127+00:00
-- url     : https://prove2.me/theorems/453f5f87-5764-4c90-b904-5179b84b088c
-- title:
--   Invariant derivations, translations, zero sets and stabilisers on $\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$, for the multiplicity estimate
-- statement:
--   Vocabulary for the multiplicity side of the elementary multiplicity estimate `MultiplicityEstimateElem`, used by the C1.3 nodes of the Diaz modulus mission. It builds on the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`): everything lives in the polynomial ring $R = K[X, Y, Z]$ = `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` with variables $X_h$ ($h \in A_0$), $Y_i$ = `inr (i, true)` and $Z_i$ = `inr (i, false)` ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_i$ is `torusIdeal`. It contains fifteen definitions and five short structural lemmas, and no theorem of substance.
--
--   **The group.** `TorusGroup K A₀ A₁` is $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ over $K$, the pairs $g = (x, y)$ with $x \in K^{A_0}$ (written multiplicatively) and $y \in (K^\times)^{A_1}$; `torusPt g` is the point $(x, y, y^{-1})$.
--
--   **Invariant derivations.** For $w = (\xi, \eta) \in K^{A_0} \times K^{A_1}$, `torusDeriv w` is the derivation
--   $$D_w = \sum_h \xi_h \frac{\partial}{\partial X_h} + \sum_i \eta_i \Bigl(Y_i \frac{\partial}{\partial Y_i} - Z_i \frac{\partial}{\partial Z_i}\Bigr)$$
--   of $R$, the lift of DALAG's invariant derivation (Lemma 8.11); `torusDerivList l` is $D_{w_1} \circ \cdots \circ D_{w_t}$ for a list $l = [w_1, \dots, w_t]$.
--
--   **Translations, ideals of points, zero sets.** `torusTransl g` is the $K$-algebra map $X_h \mapsto X_h + x_h$, $Y_i \mapsto y_i Y_i$, $Z_i \mapsto y_i^{-1} Z_i$, i.e. $f \mapsto f \circ \tau_g$; `torusVanishing S` is the ideal $I(S)$ of polynomials vanishing at every point of $S \subseteq G$; `torusZero I` is the zero set $Z_G(I) \subseteq G$ of an ideal; `torusStab I` is the stabiliser $\{g : Z_G(I)\,g \subseteq Z_G(I)\}$, as a set.
--
--   **Subgroups and sections.** `torusMono φ` is the Laurent monomial $Y^{\varphi^+} Z^{\varphi^-}$ for $\varphi \in \mathbb{Z}^{A_1}$ (the character $y^\varphi$ on $G$); `linForm a` is $\sum_h a_h X_h$; `standardSet V φ` is $\{(x, y) : x \in V,\ y^{\varphi_k} = 1 \text{ for every } k\}$, the subgroup $V \times T_\varphi$; and `sectionIdeal ℓ ψ` is $J_0 + (\sum_h \ell_{k,h} X_h)_k + (Y^{\psi_k^+} Z^{\psi_k^-} - 1)_k$.
--
--   **Vanishing and the descent.** `vanishOrd J W t` is the set of $Q \in R$ with $D_l Q \in J$ for every list $l$ of elements of the subspace $W$ of length at most $t$ (for $J = I(S)$: $Q$ vanishes to order $> t$ along $W$ on $S$). `hmePoint u a s` is the point $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i)$ of the multiplicity estimate. `obstructionSpan P W u a m n V` is the span of the $(D_{w_1} \cdots D_{w_t} P) \circ \tau_{g_s v}$ with $|s_j| \le m$, $v \in V$, $t \le n$ and $w_i \in W$: with $V = \{1\}$ it spans over $J_0$ the ideals $I_r$ of the descent of DALAG §8.4.1, and with $V = Z_G(\mathfrak{p})$ the ideal $A$ there.
--
--   **Structural lemmas.** The values of $D_w$ on the variables ($D_w X_h = \xi_h$, $D_w Y_i = \eta_i Y_i$, $D_w Z_i = -\eta_i Z_i$), `torusDerivList [] = 1`, the membership rule of `torusZero`, and `eval_torusTransl`: the value of $\sigma_g f$ at the point of $h$ is the value of $f$ at the point of $hg$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy): the invariant derivations D_w, Lemma 8.11, and their translation invariance (8.10); the stabiliser, the ideals and the vanishing conditions of the proof of Th. 8.1, §8.4.1. Written here at finite level and in coordinates on the model K[X, Y, Z] of the published Definition DiazHilbertBox. C1.3 of the Diaz modulus mission. Definitions in coordinates: 29 October 2026 (C. Perassi).

import Mathlib
import Definitions.Def_DiazHilbertBox

/-! # The group `𝔾ₐ^{A₀} × 𝔾ₘ^{A₁}`, its invariant derivations, translations, zero sets and stabilisers

The vocabulary of the multiplicity side of the elementary multiplicity estimate (DALAG Ch. 8, §8.3 and §8.4.1,
at finite level). Everything lives in the model `R = K[X, Y, Z] = MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` of
`Def_DiazHilbertBox` (`Y_i = inr (i, true)`, `Z_i = inr (i, false)`), with `J₀ = torusIdeal K A₀ A₁`.

* `TorusGroup K A₀ A₁`: `G = 𝔾ₐ^{A₀} × 𝔾ₘ^{A₁}`, written multiplicatively; `torusPt g = (x, y, y⁻¹)`.
* `torusDeriv w`: the invariant derivation `D_w` (DALAG Lemma 8.11), `w = (ξ, η)`, lifted to `R`;
  `torusDerivList l = D_{w₁} ∘ ⋯ ∘ D_{w_t}` for a list `l = [w₁, …, w_t]`.
* `torusTransl g`: the translation `f ↦ f ∘ τ_g`, with `eval_torusTransl`.
* `torusVanishing S`, `torusZero I`: the ideal `I(S)` of a set of points and the zero set `Z_G(I)` of an ideal.
* `torusStab I = {g : Z(I) · g ⊆ Z(I)}`: the stabiliser of the zero set, as a set.
* `torusMono φ = Y^{φ⁺} Z^{φ⁻}`, `linForm a = Σ a_h X_h`, `standardSet V φ = V × T_φ`.
* `sectionIdeal ℓ ψ = J₀ + (Σ_h ℓ_k h X_h)_k + (Y^{ψ_k⁺}Z^{ψ_k⁻} − 1)_k`.
* `vanishOrd J W t`: vanishing to order `> t` along `W`, relative to the ideal `J`.
* `hmePoint u a s = g_s = (Σ_j s_j u_j, Π_j a_j^{s_j})`, and `obstructionSpan`: with `V = {1}` it spans the
  descent ideal `I_r` over `J₀`, with `V = Z(𝔭)` the ideal `A` of DALAG §8.4.1.

Only definitions and structural lemmas (each a few lines) live here. -/

namespace DiazModulus

open MvPolynomial

/-- The group `G = 𝔾ₐ^{A₀} × 𝔾ₘ^{A₁}` over `K`, written multiplicatively. -/
abbrev TorusGroup (K A₀ A₁ : Type*) [Field K] := Multiplicative (A₀ → K) × (A₁ → Kˣ)

/-- The point `(x, y, y⁻¹)` of `K^{A₀ ⊕ (A₁ × Bool)}` over `g = (x, y) ∈ G`. -/
def torusPt {K A₀ A₁ : Type*} [Field K] (g : TorusGroup K A₀ A₁) : A₀ ⊕ (A₁ × Bool) → K :=
  torusPoint (Multiplicative.toAdd g.1) g.2

/-- DALAG's invariant derivation `D_w` (Lemma 8.11), lifted to `K[X, Y, Z]`:
`Σ_h ξ_h ∂/∂X_h + Σ_i η_i (Y_i ∂/∂Y_i − Z_i ∂/∂Z_i)` for `w = (ξ, η)`. -/
noncomputable def torusDeriv {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K)) :
    Derivation K (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
  mkDerivation K (Sum.elim (fun h => C (w.1 h)) fun p : A₁ × Bool =>
    if p.2 then C (w.2 p.1) * X (Sum.inr p) else -(C (w.2 p.1) * X (Sum.inr p)))

/-- `D_{w₁} ∘ ⋯ ∘ D_{w_t}` for the list `[w₁, …, w_t]`. -/
noncomputable def torusDerivList {K A₀ A₁ : Type*} [Field K]
    (l : List ((A₀ → K) × (A₁ → K))) : Module.End K (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
  (l.map fun w => (torusDeriv w).toLinearMap).prod

/-- Translation `f ↦ f ∘ τ_g` (`X ↦ X + x`, `Y ↦ y Y`, `Z ↦ y⁻¹ Z`); an `AlgEquiv` by `DiazModulus.exists_translation_algEquiv`. -/
noncomputable def torusTransl {K A₀ A₁ : Type*} [Field K] (g : TorusGroup K A₀ A₁) :
    MvPolynomial (A₀ ⊕ (A₁ × Bool)) K →ₐ[K] MvPolynomial (A₀ ⊕ (A₁ × Bool)) K :=
  aeval (Sum.elim (fun h => X (Sum.inl h) + C (Multiplicative.toAdd g.1 h))
    (fun p => C (torusPt g (Sum.inr p)) * X (Sum.inr p)))

/-- The ideal `I(S)` of a set of points of `G`, in `K[X, Y, Z]`. -/
noncomputable def torusVanishing {K A₀ A₁ : Type*} [Field K] (S : Set (TorusGroup K A₀ A₁)) :
    Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
  ⨅ g ∈ S, RingHom.ker (eval (torusPt g))

/-- The zero set `Z_G(I)` in `G` of an ideal of `K[X, Y, Z]`. -/
def torusZero {K A₀ A₁ : Type*} [Field K] (I : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) :
    Set (TorusGroup K A₀ A₁) :=
  {g | ∀ f ∈ I, eval (torusPt g) f = 0}

/-- The stabiliser `{g ∈ G : Z(I) · g ⊆ Z(I)}` of the zero set of `I` (DALAG §8.4.1, "as in §5.4"). -/
def torusStab {K A₀ A₁ : Type*} [Field K] (I : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) :
    Set (TorusGroup K A₀ A₁) :=
  {g | ∀ z ∈ torusZero I, z * g ∈ torusZero I}

/-- The Laurent monomial `Y^{φ⁺} Z^{φ⁻}` (the character `y^φ` on `G`). -/
noncomputable def torusMono {K A₀ A₁ : Type*} [Field K] [Fintype A₁] (φ : A₁ → ℤ) :
    MvPolynomial (A₀ ⊕ (A₁ × Bool)) K :=
  ∏ i, X (Sum.inr (i, true)) ^ (φ i).toNat * X (Sum.inr (i, false)) ^ (-φ i).toNat

/-- The linear form `Σ_h a_h X_h`. -/
noncomputable def linForm {K A₀ A₁ : Type*} [Field K] [Fintype A₀] (a : A₀ → K) :
    MvPolynomial (A₀ ⊕ (A₁ × Bool)) K :=
  ∑ h, C (a h) * X (Sum.inl h)

/-- The algebraic subgroup `V × T_φ` of `G`, with `T_φ = {y : y^{φ k} = 1 for all k}`. -/
def standardSet {K A₀ A₁ : Type*} [Field K] [Fintype A₁] (V : Submodule K (A₀ → K)) {ι : Type*}
    (φ : ι → A₁ → ℤ) : Set (TorusGroup K A₀ A₁) :=
  {g | Multiplicative.toAdd g.1 ∈ V ∧ ∀ k, ∏ i, g.2 i ^ φ k i = 1}

/-- The section ideal `𝔞 = J₀ + (Σ_h ℓ_k h X_h)_k + (Y^{ψ_k⁺} Z^{ψ_k⁻} − 1)_k`. -/
noncomputable def sectionIdeal {K A₀ A₁ ι κ : Type*} [Field K] [Fintype A₀] [Fintype A₁]
    (ℓ : ι → A₀ → K) (ψ : κ → A₁ → ℤ) : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
  torusIdeal K A₀ A₁ ⊔ Ideal.span (Set.range fun k => linForm (A₁ := A₁) (ℓ k))
    ⊔ Ideal.span (Set.range fun k => torusMono (A₀ := A₀) (ψ k) - 1)

/-- Vanishing to order `> t` along `W`, relative to the ideal `J`: every `D_{w₁}⋯D_{w_s} Q` with
`s ≤ t`, `wᵢ ∈ W`, lies in `J` (for `J = I(S)`: `Q` vanishes to order `> t` along `W` on `S`). -/
def vanishOrd {K A₀ A₁ : Type*} [Field K]
    (J : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) (W : Submodule K ((A₀ → K) × (A₁ → K)))
    (t : ℕ) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
  {Q | ∀ l : List ((A₀ → K) × (A₁ → K)), l.length ≤ t → (∀ w ∈ l, w ∈ W) →
    torusDerivList l Q ∈ J}

/-- The point `g_s = (Σ_j s_j u_j, Π_j a_j^{s_j})` of the multiplicity estimate. -/
noncomputable def hmePoint {K A₀ A₁ B₁ : Type*} [Field K] [Fintype B₁] (u : B₁ → A₀ → K)
    (a : B₁ → A₁ → Kˣ) (s : B₁ → ℤ) : TorusGroup K A₀ A₁ :=
  (Multiplicative.ofAdd (∑ j, (s j : K) • u j), fun i => ∏ j, a j i ^ s j)

/-- The span of §8.4.1's family: `(D_{w₁}⋯D_{w_t} P) ∘ τ_{g_s · v}` for `|s_j| ≤ m`, `v ∈ V`,
`t ≤ n`, `wᵢ ∈ W`. With `V = {1}`, `m = r M₁`, `n = r M₀` it spans `I_r` over `J₀` (0-based, so
`I_0 = J₀ + (P)`); with `V = Z(𝔭)` it spans the ideal `A`. -/
noncomputable def obstructionSpan {K A₀ A₁ B₁ : Type*} [Field K] [Fintype B₁]
    (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (W : Submodule K ((A₀ → K) × (A₁ → K)))
    (u : B₁ → A₀ → K) (a : B₁ → A₁ → Kˣ) (m n : ℕ) (V : Set (TorusGroup K A₀ A₁)) :
    Submodule K (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
  Submodule.span K {Q | ∃ s : B₁ → ℤ, (∀ j, |s j| ≤ (m : ℤ)) ∧ ∃ v ∈ V,
    ∃ l : List ((A₀ → K) × (A₁ → K)), l.length ≤ n ∧ (∀ w ∈ l, w ∈ W) ∧
      Q = torusTransl (hmePoint u a s * v) (torusDerivList l P)}

/-! Structural lemmas (each a few lines). -/

@[simp] theorem torusDeriv_X_inl {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K)) (h : A₀) :
    torusDeriv w (X (Sum.inl h) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) = C (w.1 h) := by
  simp [torusDeriv, mkDerivation_X]

@[simp] theorem torusDeriv_X_inr {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K)) (i : A₁)
    (b : Bool) :
    torusDeriv w (X (Sum.inr (i, b)) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
      = if b then C (w.2 i) * X (Sum.inr (i, b)) else -(C (w.2 i) * X (Sum.inr (i, b))) := by
  simp [torusDeriv, mkDerivation_X]

@[simp] theorem torusDerivList_nil {K A₀ A₁ : Type*} [Field K] :
    torusDerivList ([] : List ((A₀ → K) × (A₁ → K))) = 1 := rfl

theorem mem_torusZero {K A₀ A₁ : Type*} [Field K] {I : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)}
    {g : TorusGroup K A₀ A₁} : g ∈ torusZero I ↔ ∀ f ∈ I, eval (torusPt g) f = 0 := Iff.rfl

theorem eval_torusTransl {K A₀ A₁ : Type*} [Field K] (g h : TorusGroup K A₀ A₁)
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :
    eval (torusPt h) (torusTransl g f) = eval (torusPt (h * g)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [torusTransl]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, map_mul]
    congr 1
    rcases v with i | ⟨i, b⟩
    · simp [torusTransl, torusPt, torusPoint, toAdd_mul, add_comm]
    · cases b <;> simp [torusTransl, torusPt, torusPoint, mul_comm]

end DiazModulus


