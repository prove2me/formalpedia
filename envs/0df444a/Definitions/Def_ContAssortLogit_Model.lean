-- Prove2me | Definitions.Def_ContAssortLogit_Model
-- name    : ContAssortLogit_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:31.50585+00:00
-- url     : https://prove2.me/theorems/fd9be33c-9f46-407e-8148-889cb9dc8225
-- title:
--   Continuous logit assortment model: revenue function, preference class $\mathcal V$, choice law, $r(S,v)$, $\varrho^*$, $w^{-1}$, $g$, $h$, $\xi$
-- statement:
--   The full-information model of continuous assortment optimization with logit choice probabilities.
--
--   The **products** are the points of $[0,1]$; a customer either buys one product or nothing ($\emptyset$), so a (no-)purchase lies in $\mathcal X=[0,1]\cup\{\emptyset\}$. An **assortment** is a Borel set $S\subseteq[0,1]$; in the uncapacitated case $c=1$ the feasible assortments are
--   $$\mathcal S=\{S\in\mathcal B[0,1]\}.$$
--
--   1. **Revenue function.** $w:[0,1]\to[0,1]$ is continuously differentiable with $w'(x)\ge k>0$ on $[0,1]$ for some $k$; $w(x)$ is the revenue earned when product $x$ is bought.
--   2. **Class parameters.** $\overline v>\underline v>0$ with $\overline v>w(0)\big/\int_0^1(w(x)-w(0))\,dx$.
--   3. **Preference class** $\mathcal V(\underline v,\overline v,D)$: functions $v$ with $\underline v\le v(y)\le\overline v$ on $[0,1]$, differentiable on $(0,1)$ with $|v'(y)|\le D$ there, and integrable on $[0,1]$.
--   4. **Choice law.** A customer offered $S$ buys a product in a Borel set $A\subseteq S$ with probability
--   $$\mathbb P(X^S\in A)=\frac{\int_A v(x)\,dx}{1+\int_S v(x)\,dx},\qquad \mathbb P(X^S=\emptyset)=\frac{1}{1+\int_S v(x)\,dx}.$$
--   5. **Expected revenue** $r(S,v)=\dfrac{\int_S v(x)w(x)\,dx}{1+\int_S v(x)\,dx}$ and the **optimal revenue** $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$.
--   6. **Generalized inverse** $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, and $w^{-1}(\varrho)=1$ when this set is empty ($\varrho>w(1)$).
--   7. $g(y)=r([y,1],v)$, $h(\varrho)=g(w^{-1}(\varrho))$ and $\xi(y)=\dfrac{v(y)}{1+\int_y^1 v(x)\,dx}$.
--
--   This is the continuum analogue of the multinomial logit (MNL) model, with the preference function $v$ playing the role of the MNL weights; $h$ is the map whose fixed point is $\varrho^*$.
--
--   **Formalization Note.** Purchases live in `ℝ ⊕ Unit` (`Sum.inr ()` is $\emptyset$); $w,v:\mathbb R\to\mathbb R$ with all hypotheses on $[0,1]$ or $(0,1)$; the class carries a fixed derivative bound $D$ (Assumption 1(ii) asks only for a finite supremum over the class); $\varrho^*$ is a supremum (`sSup`), which the paper shows is attained; $w^{-1}:=1$ above $w(1)$ keeps the assortment $[w^{-1}(\varrho),1]=\{1\}$ a null set.
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, §3, pp.6–8 (𝒳, 𝒮, w, (1), r(S, v), Assumption 1), §4.1, p.10 (w⁻¹), §4.3, p.12 (g, h, ϱ*), App. A.1, p.37 (ξ)

import Mathlib
open MeasureTheory Set

namespace ContAssortLogit

/-- The purchase space `𝒳 = [0, 1] ∪ {∅}` of Peeters, den Boer & Mandjes (arXiv:1807.06497v4,
§3, p.6): `Sum.inl x` is the purchase of product `x`, `Sum.inr ()` is the no-purchase `∅`.

**Formalization Note.** Products are encoded as reals; the choice law below puts no mass on
`Sum.inl x` with `x ∉ [0, 1]`. `ℝ ⊕ Unit` carries Mathlib's sum σ-algebra. -/
abbrev PurchaseSpace : Type := ℝ ⊕ Unit

/-- The standing hypotheses on the marginal revenue function `w` (arXiv:1807.06497v4, §3, p.7):
"`w` is a continuously differentiable function `[0, 1] → [0, 1]` with positive derivative bounded
away from zero".

**Formalization Note.** `w : ℝ → ℝ`; only its values on `[0, 1]` matter. The derivative on the
closed interval is the one-sided derivative `derivWithin w (Icc 0 1)`. -/
def IsRevenueFn (w : ℝ → ℝ) : Prop :=
  MapsTo w (Icc 0 1) (Icc 0 1) ∧ ContDiffOn ℝ 1 w (Icc 0 1) ∧
    ∃ k : ℝ, 0 < k ∧ ∀ x ∈ Icc (0 : ℝ) 1, k ≤ derivWithin w (Icc 0 1) x

/-- The parameters of the class `𝒱` of Assumption 1 (arXiv:1807.06497v4, p.8):
`v̄ > v̲ > 0` with `v̄ > w(0) / ∫₀¹ (w(x) − w(0)) dx`. The derivative bound `D` of
Assumption 1(ii) is a further parameter of the class (see `InClass`). -/
def ClassParams (w : ℝ → ℝ) (vlo vhi : ℝ) : Prop :=
  0 < vlo ∧ vlo < vhi ∧ w 0 / (∫ x in (0 : ℝ)..1, (w x - w 0)) < vhi

/-- Membership of a preference function `v` in the class `𝒱 = 𝒱(v̲, v̄, D)` of Assumption 1
(arXiv:1807.06497v4, p.8, with p.7's "`v : [0, 1] → ℝ₊` is an integrable function"):
(i) `v̲ ≤ v(y) ≤ v̄` for all `y ∈ [0, 1]`; (ii) `v` is differentiable on `(0, 1)` with
`|v′(y)| ≤ D` there; and `v` is integrable on `[0, 1]`.

**Formalization Note.** Assumption 1(ii) asks for `sup_{y ∈ (0,1), v ∈ 𝒱} |v′(y)| < ∞`; the class is
read as having a fixed derivative bound `D`, which is a parameter of every statement. `v : ℝ → ℝ`;
only its values on `[0, 1]` matter. -/
def InClass (vlo vhi D : ℝ) (v : ℝ → ℝ) : Prop :=
  (∀ y ∈ Icc (0 : ℝ) 1, vlo ≤ v y ∧ v y ≤ vhi) ∧
    (∀ y ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ v y ∧ |deriv v y| ≤ D) ∧
    IntegrableOn v (Icc 0 1)

/-- The feasible assortments in the uncapacitated case `c = 1` (arXiv:1807.06497v4, §3, p.7, and
§4, p.10): `𝒮 = {S ∈ ℬ[0, 1] : vol(S) ≤ 1}`, i.e. all Borel subsets of `[0, 1]`. -/
def Assortments : Set (Set ℝ) := {S | MeasurableSet S ∧ S ⊆ Icc 0 1}

/-- The law of the random choice `X^S` of a customer offered assortment `S` (arXiv:1807.06497v4,
§3, eq. (1), p.7): `P(X^S ∈ A) = ∫_A v / (1 + ∫_S v)` for Borel `A ⊆ S`, and
`P(X^S = ∅) = 1 / (1 + ∫_S v)`. -/
noncomputable def choiceLaw (v : ℝ → ℝ) (S : Set ℝ) : Measure PurchaseSpace :=
  (ENNReal.ofReal (1 + ∫ x in S, v x))⁻¹ •
    (Measure.dirac (Sum.inr ()) +
      Measure.map Sum.inl ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (v x))))

/-- The expected revenue of assortment `S` (arXiv:1807.06497v4, §3, p.7):
`r(S, v) = ∫_S v(x) w(x) dx / (1 + ∫_S v(x) dx)`. -/
noncomputable def rev (w v : ℝ → ℝ) (S : Set ℝ) : ℝ :=
  (∫ x in S, v x * w x) / (1 + ∫ x in S, v x)

/-- The optimal expected revenue `ϱ* = max{r(S, v) : S ∈ 𝒮}` (arXiv:1807.06497v4, §4.3, p.12, and
App. A.1, p.35).

**Formalization Note.** Defined as the supremum `sSup`; the family is nonempty (`∅ ∈ 𝒮`) and
bounded above for `v ≥ 0` and `w ≤ 1` on `[0, 1]`, and the paper shows the maximum is attained. -/
noncomputable def optRev (w v : ℝ → ℝ) : ℝ :=
  sSup (rev w v '' Assortments)

/-- The generalized inverse `w⁻¹(ϱ) = min{x ∈ [0, 1] : w(x) ≥ ϱ}` (arXiv:1807.06497v4, §4.1, p.10).

**Formalization Note.** For `ϱ > w(1)` the set is empty; then `w⁻¹(ϱ) := 1`, so the assortment
`[w⁻¹(ϱ), 1] = {1}` is a null set. This is the continuous extension of the minimum and is what
`{1}` in the union encodes; for `ϱ ≤ w(1)` and increasing continuous `w` the union does not change
the infimum. -/
noncomputable def winv (w : ℝ → ℝ) (ϱ : ℝ) : ℝ :=
  sInf ({x ∈ Icc (0 : ℝ) 1 | ϱ ≤ w x} ∪ {1})

/-- `g(y) = r([y, 1], v)` (arXiv:1807.06497v4, §4.3, p.12, and App. A.1, p.35). -/
noncomputable def gfun (w v : ℝ → ℝ) (y : ℝ) : ℝ := rev w v (Icc y 1)

/-- `h(ϱ) = g(w⁻¹(ϱ))` (arXiv:1807.06497v4, §4.3, p.12, and App. A.1, p.35). -/
noncomputable def hfun (w v : ℝ → ℝ) (ϱ : ℝ) : ℝ := gfun w v (winv w ϱ)

/-- `ξ(y) = v(y) / (1 + ∫_y^1 v(x) dx)` (arXiv:1807.06497v4, proof of Lemma 4, p.37). -/
noncomputable def xi (v : ℝ → ℝ) (y : ℝ) : ℝ := v y / (1 + ∫ x in Icc y 1, v x)

end ContAssortLogit


