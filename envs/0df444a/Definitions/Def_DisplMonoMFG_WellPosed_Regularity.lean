-- Prove2me | Definitions.Def_DisplMonoMFG_WellPosed_Regularity
-- name    : DisplMonoMFG_WellPosed_Regularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:03.608011+00:00
-- url     : https://prove2.me/theorems/95a09ddf-bebf-49ae-a40f-37538985d652
-- title:
--   Full $\mathcal C^2$ regularity on $\mathcal P_2$ and on $\mathbb R^d\times\mathcal P_2$ (§2.2)
-- statement:
--   This file defines the regularity classes of §2.2, p. 2184.
--
--   Let $X$ be a finite-dimensional real normed space (the spatial variables) and $F$ a finite-dimensional real normed space (the values). A function $f:X\times\mathcal P_2\to F$ is **jointly continuous** if it is continuous for the product of the norm topology on $X$ and the $W_2$ topology on $\mathcal P_2$.
--
--   $f$ belongs to the full-$\mathcal C^2$ class $\mathcal C^2(X\times\mathcal P_2)$ if the following hold.
--
--   1. $f$ is jointly continuous.
--   2. $\partial_x f$ and $\partial_{xx}f$ exist and are jointly continuous.
--   3. The global versions of $\partial_\mu f(x,\mu,\tilde x)$ and $\partial_x\partial_\mu f(x,\mu,\tilde x)$ exist and are jointly continuous in $(x,\tilde x,\mu)$.
--   4. The global versions of $\partial_{\tilde x}\partial_\mu f(x,\mu,\tilde x)$ (the $\tilde x$-derivative of $\partial_\mu f$) and $\partial_{\mu\mu}f(x,\mu,\tilde x,\bar x)$ (the Lions derivative of $\mu\mapsto\partial_\mu f(x,\mu,\tilde x)$ at $\bar x$) exist and are jointly continuous.
--
--   With $X=\mathbb R^d$ this is $\mathcal C^2(\mathbb R^d\times\mathcal P_2)$. With $X=\mathbb R^d\times\mathbb R^k$ it is the class $\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^k)$ that the paper uses. The class $\mathcal C^2(\mathcal P_2)$, with no spatial variable, asks for $W_2$-continuity of $U$, a jointly continuous global Wasserstein gradient $\partial_\mu U(\mu,\tilde x)$, and jointly continuous $\partial_{\tilde x\mu}U(\mu,\tilde x)$ and $\partial_{\mu\mu}U(\mu,\tilde x,\bar x)$.
--
--   The file also defines three auxiliary notions:
--   - **bounded derivatives on a set**: every derivative listed above is bounded there in operator norm (the function itself is not bounded);
--   - **time-dependent versions**: joint continuity in $(t,x,\mu,\ldots)$ on a time interval;
--   - **uniform regularity in time**: $f(t,\cdot,\cdot)\in\mathcal C^2$ for every $t$, with all its derivatives continuous in $t$ and bounded uniformly in $t$.
--
--   It also defines the trace $\operatorname{tr}B=\sum_i B(e_i,e_i)$ of a bilinear form on $\mathbb R^d$.
--
--   These classes are the regularity assumed on the data $H,G$ in Assumptions 3.1–3.2 and the regularity $\mathcal C^{1,2,2}(\Theta)$ of classical solutions.
--
--   **Formalization Note** Derivatives are (multi)linear maps. The page's convention $\partial_{x\mu}U:=\partial_x[(\partial_\mu U)^\top]$ (p. 2185) is encoded as $\langle\partial_{x\mu}U(x,\mu,\tilde x)b,a\rangle=$ `DxDm x μ x̃ a b`, with the $x$-direction $a$ first. The page's "unique jointly continuous extension" is a jointly continuous witness defined on all of $X\times\mathcal P_2\times\mathbb R^d$. The paper uses $\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^k)$ without defining it; here it is the class on $X\times\mathcal P_2$ with all Euclidean variables lumped into $X$. Matrix and multilinear norms are operator norms, since the page's $|\cdot|$ on matrices is unspecified.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), §2.2, pp. 2183–2185

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Space

open MeasureTheory

/-! Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022), §2.2, pp. 2183–2185 (PDF pp. 6–8):
joint continuity on `ℝ^k × 𝒫₂`, the full-`𝒞²` classes `𝒞²(𝒫₂)` and `𝒞²(ℝ^d × 𝒫₂)` (and their
extension to `ℝ^k × 𝒫₂`), bounds on derivatives, and the time-dependent versions used in
`𝒞^{1,2,2}(Θ)` and in Theorem 4.1. -/

namespace DisplMonoMFG.WellPosed

variable {d : ℕ}

/-- The `i`-th standard basis vector `eᵢ` of `ℝ^d`. -/
noncomputable abbrev e (i : Fin d) : E d := EuclideanSpace.single i 1

/-- The trace `tr B = ∑ᵢ B(eᵢ, eᵢ)` of a bilinear form on `ℝ^d` (the trace of its matrix). -/
noncomputable def tr (B : E d →L[ℝ] E d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (e i) (e i)

/-- Joint continuity of `f : X × 𝒫₂ → F` for the product of the norm topology of the
finite-dimensional space `X` and the `W₂` topology. -/
def ContXP {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F]
    (f : X → P2 d → F) : Prop :=
  ∀ x : X, ∀ μ : P2 d, ∀ ε > 0, ∃ δ > 0, ∀ x' : X, ∀ μ' : P2 d,
    ‖x' - x‖ + W2 μ μ' < δ → ‖f x' μ' - f x μ‖ < ε

/-- Joint continuity of `f : I × X × 𝒫₂ → F` on a time set `I`. -/
def ContTXP {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F]
    (I : Set ℝ) (f : ℝ → X → P2 d → F) : Prop :=
  ∀ t ∈ I, ∀ x : X, ∀ μ : P2 d, ∀ ε > 0, ∃ δ > 0, ∀ t' ∈ I, ∀ x' : X, ∀ μ' : P2 d,
    |t' - t| + ‖x' - x‖ + W2 μ μ' < δ → ‖f t' x' μ' - f t x μ‖ < ε

/-- The witnesses of full-`𝒞²` regularity of `U : X × 𝒫₂ → F` (p. 2184), as global versions:
`Dx = ∂_x U(x, μ)`, `Dxx = ∂_xx U(x, μ)`, `Dm = ∂_μ U(x, μ, x̃)`, `DxDm = ∂_x∂_μ U(x, μ, x̃)`,
`DyDm = ∂_x̃∂_μ U(x, μ, x̃)` and `Dmm = ∂_μμ U(x, μ, x̃, x̄)`. Derivatives are (multi)linear
maps; `DxDm x μ x̃ a b` takes the `x`-direction `a` first and the `μ`-direction `b` second, so
`⟨∂_xμ U(x, μ, x̃) b, a⟩ = DxDm x μ x̃ a b` (p. 2185: `∂_xμ U := ∂_x[(∂_μ U)ᵀ]`).
`Dmm x μ x̃ x̄ a b` is the Lions derivative of `μ ↦ Dm x μ x̃` at the point `x̄`, applied first to
the `x̄`-direction `a`, then to the `x̃`-direction `b`. -/
structure C2W (d : ℕ) (X F : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  Dx : X → P2 d → (X →L[ℝ] F)
  Dxx : X → P2 d → (X →L[ℝ] X →L[ℝ] F)
  Dm : X → P2 d → E d → (E d →L[ℝ] F)
  DxDm : X → P2 d → E d → (X →L[ℝ] E d →L[ℝ] F)
  DyDm : X → P2 d → E d → (E d →L[ℝ] E d →L[ℝ] F)
  Dmm : X → P2 d → E d → E d → (E d →L[ℝ] E d →L[ℝ] F)

/-- Full `𝒞²` regularity, p. 2184, items (i)–(iii): `U` is jointly continuous; `∂_x U`, `∂_xx U`
exist and are jointly continuous; the global versions of `∂_μ U` and `∂_x∂_μ U` exist and are
jointly continuous; and the global versions of `∂_x̃∂_μ U` and `∂_μμ U` exist and are jointly
continuous, all with the witnesses `w`. With `X = ℝ^d` this is `𝒞²(ℝ^d × 𝒫₂)`. Formalization
Note: with `X = ℝ^d × ℝ^k` (all Euclidean arguments lumped into one spatial variable) it is the
paper's `𝒞²(ℝ^d × 𝒫₂ × ℝ^k)`, which the page uses without defining it. -/
def IsC2With {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : X → P2 d → F) (w : C2W d X F) : Prop :=
  ContXP f ∧
  (∀ x μ, HasFDerivAt (fun y => f y μ) (w.Dx x μ) x) ∧
  (∀ x μ, HasFDerivAt (fun y => w.Dx y μ) (w.Dxx x μ) x) ∧
  (∀ x, HasLDeriv (f x) (w.Dm x)) ∧
  (∀ x μ y, HasFDerivAt (fun x' => w.Dm x' μ y) (w.DxDm x μ y) x) ∧
  (∀ x μ y, HasFDerivAt (fun y' => w.Dm x μ y') (w.DyDm x μ y) y) ∧
  (∀ x y, HasLDeriv (fun μ => w.Dm x μ y) (fun μ y' => w.Dmm x μ y y')) ∧
  ContXP w.Dx ∧ ContXP w.Dxx ∧
  ContXP (fun (q : X × E d) μ => w.Dm q.1 μ q.2) ∧
  ContXP (fun (q : X × E d) μ => w.DxDm q.1 μ q.2) ∧
  ContXP (fun (q : X × E d) μ => w.DyDm q.1 μ q.2) ∧
  ContXP (fun (q : X × E d × E d) μ => w.Dmm q.1 μ q.2.1 q.2.2)

/-- Every derivative witness of `w` has norm at most `C` at every spatial point satisfying `S`
(for all measures and all `x̃`, `x̄`). `S = fun _ => True` is "the supremum norms of all their
derivatives are uniformly bounded"; `S (x, p) := ‖p‖ ≤ R` is "bounded on `D_R`". The function
itself is not bounded. -/
def C2W.BddOn {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : C2W d X F) (S : X → Prop) (C : ℝ) : Prop :=
  ∀ x, S x → ∀ (μ : P2 d) (y z : E d),
    ‖w.Dx x μ‖ ≤ C ∧ ‖w.Dxx x μ‖ ≤ C ∧ ‖w.Dm x μ y‖ ≤ C ∧ ‖w.DxDm x μ y‖ ≤ C ∧
    ‖w.DyDm x μ y‖ ≤ C ∧ ‖w.Dmm x μ y z‖ ≤ C

/-- `𝒞²(𝒫₂)`, pp. 2183–2184 (no spatial variable): `U` is `W₂`-continuous, has a global
Wasserstein gradient `Dm`, and `Dm` has jointly continuous derivatives `DyDm = ∂_x̃μ U(μ, x̃)`
(in `x̃`) and `Dmm = ∂_μμ U(μ, x̃, x̄)` (Lions derivative of `μ ↦ Dm μ x̃` at `x̄`, applied first to
the `x̄`-direction); `Dm`, `DyDm`, `Dmm` are jointly continuous. -/
def IsC2P (U : P2 d → ℝ) (Dm : P2 d → E d → (E d →L[ℝ] ℝ))
    (DyDm : P2 d → E d → (E d →L[ℝ] E d →L[ℝ] ℝ))
    (Dmm : P2 d → E d → E d → (E d →L[ℝ] E d →L[ℝ] ℝ)) : Prop :=
  ContP U ∧ HasLDeriv U Dm ∧
  (∀ μ y, HasFDerivAt (fun y' => Dm μ y') (DyDm μ y) y) ∧
  (∀ y, HasLDeriv (fun μ => Dm μ y) (fun μ y' => Dmm μ y y')) ∧
  ContXP (fun (y : E d) μ => Dm μ y) ∧ ContXP (fun (y : E d) μ => DyDm μ y) ∧
  ContXP (fun (q : E d × E d) μ => Dmm μ q.1 q.2)

/-- Joint continuity in `(t, x, μ, x̃, x̄)` on `I` of all six witnesses of a time-indexed family. -/
def C2W.ContT {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (I : Set ℝ) (w : ℝ → C2W d X F) : Prop :=
  ContTXP I (fun t x μ => (w t).Dx x μ) ∧ ContTXP I (fun t x μ => (w t).Dxx x μ) ∧
  ContTXP I (fun t (q : X × E d) μ => (w t).Dm q.1 μ q.2) ∧
  ContTXP I (fun t (q : X × E d) μ => (w t).DxDm q.1 μ q.2) ∧
  ContTXP I (fun t (q : X × E d) μ => (w t).DyDm q.1 μ q.2) ∧
  ContTXP I (fun t (q : X × E d × E d) μ => (w t).Dmm q.1 μ q.2.1 q.2.2)

/-- `f(t, ·, ·) ∈ 𝒞²(X × 𝒫₂)` for every `t ∈ I` with witnesses `w t`, and all these derivatives
are also continuous in time and uniformly bounded on `I` (one bound for all `t ∈ I`). -/
def IsC2T {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (I : Set ℝ) (f : ℝ → X → P2 d → F) (w : ℝ → C2W d X F) : Prop :=
  (∀ t ∈ I, IsC2With (f t) (w t)) ∧ C2W.ContT I w ∧
  ∃ C : ℝ, ∀ t ∈ I, (w t).BddOn (fun _ => True) C

end DisplMonoMFG.WellPosed


