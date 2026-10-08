-- Prove2me | Definitions.Def_DisplMonoMFG_WellPosed_Hyp
-- name    : DisplMonoMFG_WellPosed_Hyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:30.944232+00:00
-- url     : https://prove2.me/theorems/c2537c0d-61bb-4794-9f99-95bb154693ef
-- title:
--   Assumptions 3.1, 3.2 and 3.5 on the terminal cost $G$ and the Hamiltonian $H$
-- statement:
--   Let $G:\mathbb R^d\times\mathcal P_2\to\mathbb R$ and $H:\mathbb R^d\times\mathcal P_2\times\mathbb R^d\to\mathbb R$. Write $B_R=\{p:|p|\le R\}$ and $D_R=\mathbb R^d\times\mathcal P_2\times B_R$.
--
--   **Assumption 3.1** (p. 2190).
--   1. $G\in\mathcal C^2(\mathbb R^d\times\mathcal P_2)$ with $|\partial_xG|,|\partial_{xx}G|\le L_0^G$ and $|\partial_\mu G|,|\partial_{x\mu}G|\le L_1^G$.
--   2. $G,\partial_xG,\partial_{xx}G\in\mathcal C^2(\mathbb R^d\times\mathcal P_2)$ and $\partial_\mu G,\partial_{x\mu}G\in\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^d)$, with all their derivatives uniformly bounded.
--
--   **Remark 3.3(ii)**. $L_2^G$ is a constant such that $G$ and $\partial_xG$ are $L_2^G$-Lipschitz in $\mu$ under $W_2$, uniformly in $x$.
--
--   **Assumption 3.2** (p. 2190).
--   1. $H\in\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^d)$, and for every $R>0$ there is $L^H(R)$ such that $|\partial_xH|,|\partial_pH|,|\partial_{xx}H|,|\partial_{xp}H|,|\partial_{pp}H|\le L^H(R)$ on $D_R$ and $|\partial_\mu H|,|\partial_{x\mu}H|,|\partial_{p\mu}H|\le L^H(R)$ on $\mathbb R^d\times\mathcal P_2\times\mathbb R^d\times B_R$.
--   2. $H\in\mathcal C^3$, and $H,\partial_xH,\partial_pH,\partial_{xx}H,\partial_{xp}H,\partial_{pp}H,\partial_{xxp}H,\partial_{xpp}H,\partial_{ppp}H\in\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^d)$ with all their derivatives bounded on $D_R$. Moreover, $\partial_\mu H,\partial_{x\mu}H,\partial_{p\mu}H,\partial_{xp\mu}H,\partial_{pp\mu}H\in\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^{2d})$ with all their derivatives bounded on $\mathbb R^d\times\mathcal P_2\times\mathbb R^d\times B_R$.
--   3. There is $C_0>0$ with $|\partial_xH(x,\mu,p)|\le C_0(1+|p|)$.
--   4. $H$ is strictly convex in $p$, and for every $R>0$
--   $$
--   \big|(\partial_{pp}H(x,\mu,p))^{-1/2}\,\partial_{p\mu}H(x,\mu,\tilde x,p)\big|\le L^H(R)\qquad\text{on }\mathbb R^d\times\mathcal P_2\times\mathbb R^d\times B_R.
--   $$
--
--   **Assumption 3.5** (p. 2191). $G$ satisfies (2.16) and $H$ satisfies (3.2). Its regularity parts, 3.1(i) and 3.2(i), (iv), are stated through the definitions above.
--
--   These are the standing hypotheses of the paper's main results.
--
--   **Formalization Note** $H$ is handled through its lift $((x,p),\mu)\mapsto H(x,\mu,p)$, and partial derivatives in $x$ and $p$ are restrictions of the $(x,p)$-derivatives. The page defines $\mathcal C^k$ only for $k\in\{1,2\}$, so "$H\in\mathcal C^3$" is read as: the $(x,p)$-derivatives up to order three exist and are jointly continuous. Memberships of vector- or matrix-valued functions in $\mathcal C^2$ are stated coordinatewise, which is equivalent. Only the listed functions are required to be $\mathcal C^2$. Assumption 3.2(iv) adds that $\partial_{pp}H$ is positive definite, which the page's $(\partial_{pp}H)^{-1/2}$ presupposes. Its bound is written $\langle(\partial_{pp}H)^{-1}Bv,Bv\rangle\le L^H(R)^2|v|^2$ with $Bv=\partial_{p\mu}H\,v$ and $L^H(R)\ge0$. The same $L^H$ serves (i) and (iv), as on the page. Remark 3.3's constant is used in its Lipschitz form; under Assumption 3.1 such a constant exists.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), Assumptions 3.1, 3.2, Remark 3.3, Assumption 3.5, pp. 2190–2191

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Monotone

open MeasureTheory Matrix

/-! Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022), §3, pp. 2190–2191 (PDF pp. 13–14):
Assumption 3.1 on the terminal cost `G`, Assumption 3.2 on the Hamiltonian `H`, the
`W₂`-Lipschitz constant `L₂^G` of Remark 3.3(ii), and Assumption 3.5 (displacement monotonicity
of `G` and `H`). `H(x, μ, p)` is handled through its lift `((x, p), μ) ↦ H(x, μ, p)` on
`(ℝ^d × ℝ^d) × 𝒫₂` with `𝒞²` witnesses `wH`; `B_R = {|p| ≤ R}`, `D_R = ℝ^d × 𝒫₂ × B_R` ((2.9),
p. 2184). -/

namespace DisplMonoMFG.WellPosed

variable {d : ℕ}

/-- The lift `((x, p), μ) ↦ H(x, μ, p)` of a Hamiltonian `H : ℝ^d × 𝒫₂ × ℝ^d → ℝ`. -/
def liftH (H : E d → P2 d → E d → ℝ) : E d × E d → P2 d → ℝ :=
  fun xp μ => H xp.1 μ xp.2

/-- The embedding `u ↦ (u, 0)` of the `x`-directions. -/
noncomputable abbrev Lx : E d →L[ℝ] E d × E d := ContinuousLinearMap.inl ℝ (E d) (E d)

/-- The embedding `v ↦ (0, v)` of the `p`-directions. -/
noncomputable abbrev Lp : E d →L[ℝ] E d × E d := ContinuousLinearMap.inr ℝ (E d) (E d)

/-- `f ∈ 𝒞²(X × 𝒫₂)` (some witnesses `w`) and, for each `R > 0`, the supremum norms of all its
derivatives are bounded on `{x : S R x}`. With `S R = fun _ => True` this is "the supremum norms
of all their derivatives are uniformly bounded". -/
def C2Bdd {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → P2 d → ℝ) (S : ℝ → X → Prop) : Prop :=
  ∃ w : C2W d X ℝ, IsC2With f w ∧ ∀ R > 0, ∃ C : ℝ, w.BddOn (S R) C

/-- Assumption 3.1(i), p. 2190: `G ∈ 𝒞²(ℝ^d × 𝒫₂)` (witnesses `wG`) with
`|∂_x G|, |∂_xx G| ≤ L₀^G` and `|∂_μ G|, |∂_xμ G| ≤ L₁^G` everywhere. -/
def Assm31i (G : E d → P2 d → ℝ) (wG : C2W d (E d) ℝ) (L0 L1 : ℝ) : Prop :=
  IsC2With G wG ∧ ∀ (x : E d) (μ : P2 d),
    ‖wG.Dx x μ‖ ≤ L0 ∧ ‖wG.Dxx x μ‖ ≤ L0 ∧
    ∀ y : E d, ‖wG.Dm x μ y‖ ≤ L1 ∧ ‖wG.DxDm x μ y‖ ≤ L1

/-- Assumption 3.1(ii), p. 2190: `G, ∂_x G, ∂_xx G ∈ 𝒞²(ℝ^d × 𝒫₂)` and
`∂_μ G, ∂_xμ G ∈ 𝒞²(ℝ^d × 𝒫₂ × ℝ^d)` (as functions of `((x, x̃), μ)`), and the supremum norms of
all their derivatives are uniformly bounded. Formalization Note: a function with values in
`ℝ^d` or `ℝ^{d×d}` is in `𝒞²` with bounded derivatives iff each coordinate is, so the
memberships are stated coordinatewise (`∂_{x_i} G`, `∂_{x_i x_j} G`, `(∂_μ G)_k`,
`(∂_xμ G)_{ik}`). -/
def Assm31ii (G : E d → P2 d → ℝ) (wG : C2W d (E d) ℝ) : Prop :=
  C2Bdd G (fun _ _ => True) ∧
  (∀ i, C2Bdd (fun x μ => wG.Dx x μ (e i)) (fun _ _ => True)) ∧
  (∀ i j, C2Bdd (fun x μ => wG.Dxx x μ (e i) (e j)) (fun _ _ => True)) ∧
  (∀ k, C2Bdd (fun (q : E d × E d) μ => wG.Dm q.1 μ q.2 (e k)) (fun _ _ => True)) ∧
  (∀ i k, C2Bdd (fun (q : E d × E d) μ => wG.DxDm q.1 μ q.2 (e i) (e k)) (fun _ _ => True))

/-- Assumption 3.1 (both parts), with some constants `L₀^G`, `L₁^G`. -/
def Assm31 (G : E d → P2 d → ℝ) (wG : C2W d (E d) ℝ) : Prop :=
  ∃ L0 L1 : ℝ, Assm31i G wG L0 L1 ∧ Assm31ii G wG

/-- Remark 3.3(ii), (3.1), p. 2190: `G` and `∂_x G` are Lipschitz in `μ` under `W₂`, uniformly in
`x`, with constant `L₂^G`. Formalization Note: the page defines `L₂^G` as this Lipschitz constant
and displays its derivative form (3.1); the Lipschitz form is used. Under Assumption 3.1 such a
constant exists (`L₂^G ≤ L₁^G`), so the hypothesis only names it. -/
def LipW2 (G : E d → P2 d → ℝ) (wG : C2W d (E d) ℝ) (L2 : ℝ) : Prop :=
  ∀ (x : E d) (μ ν : P2 d),
    |G x μ - G x ν| ≤ L2 * W2 μ ν ∧ ‖wG.Dx x μ - wG.Dx x ν‖ ≤ L2 * W2 μ ν

/-- The bounds of Assumption 3.2(i) at radius `R` with constant `L`:
`|∂_x H|, |∂_p H|, |∂_xx H|, |∂_xp H|, |∂_pp H| ≤ L` on `D_R` and
`|∂_μ H|, |∂_xμ H|, |∂_pμ H| ≤ L` on `ℝ^d × 𝒫₂ × ℝ^d × B_R`. -/
def H32iBd (wH : C2W d (E d × E d) ℝ) (R L : ℝ) : Prop :=
  ∀ (x p : E d) (μ : P2 d), ‖p‖ ≤ R →
    ‖(wH.Dx (x, p) μ).comp Lx‖ ≤ L ∧ ‖(wH.Dx (x, p) μ).comp Lp‖ ≤ L ∧
    ‖(wH.Dxx (x, p) μ).bilinearComp Lx Lx‖ ≤ L ∧
    ‖(wH.Dxx (x, p) μ).bilinearComp Lx Lp‖ ≤ L ∧
    ‖(wH.Dxx (x, p) μ).bilinearComp Lp Lp‖ ≤ L ∧
    ∀ y : E d, ‖wH.Dm (x, p) μ y‖ ≤ L ∧
      ‖(wH.DxDm (x, p) μ y).comp Lx‖ ≤ L ∧ ‖(wH.DxDm (x, p) μ y).comp Lp‖ ≤ L

/-- Assumption 3.2(i), p. 2190: `H ∈ 𝒞²(ℝ^d × 𝒫₂ × ℝ^d)` (witnesses `wH` of the lift) and, for
every `R > 0`, the bounds of `H32iBd` hold with constant `L^H(R)`. -/
def Assm32i (H : E d → P2 d → E d → ℝ) (wH : C2W d (E d × E d) ℝ) (LH : ℝ → ℝ) : Prop :=
  IsC2With (liftH H) wH ∧ ∀ R > 0, H32iBd wH R (LH R)

/-- Assumption 3.2(ii), p. 2190. "`H ∈ 𝒞³`" is read as: the `(x, p)`-derivatives of `H` up to
order three exist and are jointly continuous: for all directions `a, b`, the function
`((x, p), μ) ↦ ∂²_{(x,p)} H(x, μ, p)(a, b)` has `(x, p)`-derivative `D3 a b` (so
`D3 a b (x, p) μ c` is the third derivative in the directions `c, a, b`), jointly continuous. Then
`H, ∂_x H, ∂_p H, ∂_xx H, ∂_xp H, ∂_pp H, ∂_xxp H, ∂_xpp H, ∂_ppp H ∈ 𝒞²(ℝ^d × 𝒫₂ × ℝ^d)` with
all their derivatives bounded on `D_R` (for each `R > 0`), and
`∂_μ H, ∂_xμ H, ∂_pμ H, ∂_xpμ H, ∂_ppμ H ∈ 𝒞²(ℝ^d × 𝒫₂ × ℝ^{2d})`, as functions of
`((x, x̃, p), μ)`, with all their derivatives bounded on `ℝ^d × 𝒫₂ × ℝ^d × B_R`. `∂_xpμ H` and
`∂_ppμ H` are the `x`- and `p`-derivatives of `∂_pμ H` (witnesses `wpm`). Formalization Note: the
page defines `𝒞^k` only for `k ∈ {1, 2}`; the reading of `𝒞³` and the coordinatewise statement
of the memberships (equivalent for finite-dimensional values) are disclosed. Only the listed
functions are required to be `𝒞²`. -/
def Assm32ii (H : E d → P2 d → E d → ℝ) (wH : C2W d (E d × E d) ℝ) : Prop :=
  ∃ D3 : E d × E d → E d × E d → E d × E d → P2 d → (E d × E d →L[ℝ] ℝ),
    (∀ a b xp μ, HasFDerivAt (fun y => wH.Dxx y μ a b) (D3 a b xp μ) xp) ∧
    (∀ a b, ContXP (D3 a b)) ∧
    -- the nine functions of `(x, p), μ`, derivatives bounded on `D_R`
    C2Bdd (liftH H) (fun R xp => ‖xp.2‖ ≤ R) ∧
    (∀ i, C2Bdd (fun xp μ => wH.Dx xp μ (Lx (e i))) (fun R xp => ‖xp.2‖ ≤ R)) ∧
    (∀ i, C2Bdd (fun xp μ => wH.Dx xp μ (Lp (e i))) (fun R xp => ‖xp.2‖ ≤ R)) ∧
    (∀ i j, C2Bdd (fun xp μ => wH.Dxx xp μ (Lx (e i)) (Lx (e j))) (fun R xp => ‖xp.2‖ ≤ R)) ∧
    (∀ i j, C2Bdd (fun xp μ => wH.Dxx xp μ (Lx (e i)) (Lp (e j))) (fun R xp => ‖xp.2‖ ≤ R)) ∧
    (∀ i j, C2Bdd (fun xp μ => wH.Dxx xp μ (Lp (e i)) (Lp (e j))) (fun R xp => ‖xp.2‖ ≤ R)) ∧
    (∀ i j k, C2Bdd (fun xp μ => D3 (Lx (e i)) (Lx (e j)) xp μ (Lp (e k)))
      (fun R xp => ‖xp.2‖ ≤ R)) ∧
    (∀ i j k, C2Bdd (fun xp μ => D3 (Lx (e i)) (Lp (e j)) xp μ (Lp (e k)))
      (fun R xp => ‖xp.2‖ ≤ R)) ∧
    (∀ i j k, C2Bdd (fun xp μ => D3 (Lp (e i)) (Lp (e j)) xp μ (Lp (e k)))
      (fun R xp => ‖xp.2‖ ≤ R)) ∧
    -- the five functions of `(x, x̃, p), μ`, derivatives bounded on `ℝ^d × 𝒫₂ × ℝ^d × B_R`
    (∀ k, C2Bdd (fun (q : E d × E d × E d) μ => wH.Dm (q.1, q.2.2) μ q.2.1 (e k))
      (fun R q => ‖q.2.2‖ ≤ R)) ∧
    (∀ i k, C2Bdd (fun (q : E d × E d × E d) μ => wH.DxDm (q.1, q.2.2) μ q.2.1 (Lx (e i)) (e k))
      (fun R q => ‖q.2.2‖ ≤ R)) ∧
    ∃ wpm : Fin d → Fin d → C2W d (E d × E d × E d) ℝ,
      (∀ i k, IsC2With (fun (q : E d × E d × E d) μ =>
          wH.DxDm (q.1, q.2.2) μ q.2.1 (Lp (e i)) (e k)) (wpm i k) ∧
        ∀ R > 0, ∃ C : ℝ, (wpm i k).BddOn (fun q => ‖q.2.2‖ ≤ R) C) ∧
      (∀ i k j, C2Bdd (fun (q : E d × E d × E d) μ => (wpm i k).Dx q μ (e j, 0, 0))
        (fun R q => ‖q.2.2‖ ≤ R)) ∧
      (∀ i k j, C2Bdd (fun (q : E d × E d × E d) μ => (wpm i k).Dx q μ (0, 0, e j))
        (fun R q => ‖q.2.2‖ ≤ R))

/-- Assumption 3.2(iii), p. 2190: there is `C₀ > 0` with `|∂_x H(x, μ, p)| ≤ C₀(1 + |p|)`. -/
def Assm32iii (wH : C2W d (E d × E d) ℝ) (C0 : ℝ) : Prop :=
  0 < C0 ∧ ∀ (x p : E d) (μ : P2 d), ‖(wH.Dx (x, p) μ).comp Lx‖ ≤ C0 * (1 + ‖p‖)

/-- The bound of Assumption 3.2(iv) at radius `R` with constant `L`:
`|(∂_pp H(x, μ, p))^{-1/2} ∂_pμ H(x, μ, x̃, p)| ≤ L` on `ℝ^d × 𝒫₂ × ℝ^d × B_R` (operator norm),
written `⟨A⁻¹ B v, B v⟩ ≤ L² |v|²` with `A = ∂_pp H(x, μ, p)`, `B v = ∂_pμ H(x, μ, x̃, p) v`,
together with `0 ≤ L`; for positive definite `A` this is `|A^{-1/2} B| ≤ L`. -/
def H32ivBd (wH : C2W d (E d × E d) ℝ) (R L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ (x p y : E d) (μ : P2 d), ‖p‖ ≤ R → ∀ v : E d,
    (fun i => wH.DxDm (x, p) μ y (Lp (e i)) v) ⬝ᵥ
      ((ppMat wH x p μ)⁻¹ *ᵥ (fun i => wH.DxDm (x, p) μ y (Lp (e i)) v)) ≤ L ^ 2 * ‖v‖ ^ 2

/-- Assumption 3.2(iv), p. 2190: `H` is strictly convex in `p`, and for every `R > 0`,
`|(∂_pp H(x, μ, p))^{-1/2} ∂_pμ H(x, μ, x̃, p)| ≤ L^H(R)` on `ℝ^d × 𝒫₂ × ℝ^d × B_R` (operator
norm, `H32ivBd`). Formalization Notes: `∂_pp H` is positive definite everywhere (implicit in the
page's use of `(∂_pp H)^{-1/2}`), so `⁻¹` is the true inverse; `|A^{-1/2} B v|² = ⟨A⁻¹ B v, B v⟩`
for symmetric positive definite `A`. -/
def Assm32iv (H : E d → P2 d → E d → ℝ) (wH : C2W d (E d × E d) ℝ) (LH : ℝ → ℝ) : Prop :=
  (∀ (x : E d) (μ : P2 d), StrictConvexOn ℝ Set.univ (H x μ)) ∧
  (∀ (x p : E d) (μ : P2 d), (ppMat wH x p μ).PosDef) ∧
  ∀ R > 0, H32ivBd wH R (LH R)

/-- Assumption 3.2 (all four parts), with some `L^H` and `C₀` (the same `L^H` in (i) and (iv),
as on the page). -/
def Assm32 (H : E d → P2 d → E d → ℝ) (wH : C2W d (E d × E d) ℝ) : Prop :=
  ∃ (LH : ℝ → ℝ) (C0 : ℝ),
    Assm32i H wH LH ∧ Assm32ii H wH ∧ Assm32iii wH C0 ∧ Assm32iv H wH LH

/-- The displacement monotonicity part of Assumption 3.5, p. 2191: (i) `G` satisfies (2.16);
(ii) `H` satisfies (3.2). (The regularity parts, Assumptions 3.1(i) and 3.2(i), (iv), are stated
separately.) -/
def Assm35 (wG : C2W d (E d) ℝ) (wH : C2W d (E d × E d) ℝ) : Prop :=
  DisplMono wG ∧ DisplMonoH wH

end DisplMonoMFG.WellPosed


