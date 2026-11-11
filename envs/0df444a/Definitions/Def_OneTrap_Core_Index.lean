-- Prove2me | Definitions.Def_OneTrap_Core_Index
-- name    : OneTrap_Core_Index
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:45:49.076341+00:00
-- url     : https://prove2.me/theorems/4f278380-8a27-4543-81fc-7df6a4d04e09
-- title:
--   Reservation values $\rho_i$, covered wages, the state update $(M_i,\widehat H_i)$, index policies and dynamically consistent policies
-- statement:
--   For a contract $w$ and a box with output $Y$, the wage is $X=w(Y)$ and the residual $H=Y-w(Y)$. The **reservation value** (index) $\rho$ of a box with cost $c$ is the smallest extended-real solution of $c=\mathbb E[(X-\rho)^+]$ with $(X-\infty)^+:=0$ (eq. (16)); for $c>0$ it is finite, for $c=0$ it is $\operatorname{ess\,sup}X$, possibly $+\infty$. The **covered wage** is $X^{\mathrm{cov}}=\min\{X,\rho\}$. When a box realizes $(X_i,H_i)$ at incumbent $(x,h)$, the new incumbent is $(M_i,\widehat H_i)$ with $M_i=\max\{x,X_i\}$ and $\widehat H_i=h$, $\max\{h,H_i\}$ or $H_i$ according as $X_i<x$, $X_i=x$ or $X_i>x$ (§B.1.1). The Bellman opening values are $u_i=-c_i+\mathbb E[U(R\setminus\{i\},M_i,\widehat H_i)]$ and $p_i=\mathbb E[P(R\setminus\{i\},M_i,\widehat H_i)]$ (eq. (17)). An **index policy** from wage $x$ opens a box of largest remaining index while the highest available wage is below that index and otherwise stops on an outcome of highest wage (Lemma B.3). A policy is **dynamically consistent** if after every history its decision attains the lexicographic Bellman maximum (17) at the current state (Lemma B.1).
--
--   **Formalization Note** `resvOf w F c = sInf {r : EReal | ∫⁻ y, ((w y : EReal) − r).toENNReal ∂F = ofReal c}` (`EReal` subtraction makes $(X-\infty)^+=0$; `sInf ∅ = ⊤`, reached only for non-integrable wages, outside $W_{\mathrm{eff}}$); `resv w b` applies it to a box. `coveredWage` is `min (w y) ρ` in `EReal`. `updState` is $(M_i,\widehat H_i)$ case by case; `lexMax` is the lexicographic maximum of two pairs, `stateAfter w p₀ S y` folds it over the opened boxes (the result does not depend on the fold order), and `curWage` is the highest available wage. `openU`/`openP` are $u_i$, $p_i$ with `eexp` over $F_i$. `IsIndexPolicy w T x π` compares the current wage with `(univ \ S).sup ρ` (`⊥` when nothing remains, `⊤` when an infinite-index box remains). `IsDynConsistent w T π` requires, at every opened set `S` with state `stateAfter w (w 0, 0 − w 0) S y`, that an opened box attain $(U,P)$ through $(u_i,p_i)$ and that stopping attain it and submit the incumbent pair.
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), §3.1, p. 6 (PDF 7); eq. (16)–(17) and Lemma B.1, p. 22 (PDF 23); Lemma B.3, p. 23 (PDF 24), and its proof, pp. 32–33 (PDF 33–34)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search

/-!
# Reservation values, covered wages, Bellman state updates and decision rules

Feldman, Fu, Peng, Tang (2026), held STOC 2027 submission, §3.1 (p. 6), eq. (16) and
§B.1.1 (p. 22), Lemma B.1 (p. 22), Lemma B.3 (p. 23).

For a contract `w`, box `i` has wage `X_i = w(Y_i)` and residual `H_i = Y_i − w(Y_i)`. Its
reservation value (index) `ρ_i` is the smallest extended-real solution `r` of
`c_i = E[(X_i − r)⁺]`, with `(X − ∞)⁺ := 0`.
-/

noncomputable section

open MeasureTheory

namespace OneTrap.Core

/-- The reservation value of an output law `F` at cost `c` under the contract `w` (eq. (16),
p. 22): the smallest extended-real `r` with `E[(w(Y) − r)⁺] = c`, where `Y ∼ F` and
`(X − ∞)⁺ = 0` (in `EReal`, `X − ⊤ = ⊥`, whose positive part is `0`). The expectation is a
lower Lebesgue integral in `[0, ∞]`; `sInf ∅ = ⊤`. -/
def resvOf (w : ℝ → ℝ) (F : OutputLaw) (c : ℝ) : EReal :=
  sInf {r : EReal | ∫⁻ y, (((w y : ℝ) : EReal) - r).toENNReal ∂(F.law : Measure ℝ) =
    ENNReal.ofReal c}

/-- The reservation value `ρ_i` of a box. -/
def resv (w : ℝ → ℝ) (b : Box) : EReal :=
  resvOf w b.out b.cost

/-- The covered wage `X^cov_i = min {X_i, ρ_i}` of a box at output `y` (Lemma B.3, p. 23);
it equals `X_i` when `ρ_i = +∞`. -/
def coveredWage (w : ℝ → ℝ) (b : Box) (y : ℝ) : EReal :=
  min ((w y : ℝ) : EReal) (resv w b)

/-- The state update of §B.1.1 (p. 22): when box `i` realizes output `y` (wage `X_i = w(y)`,
residual `H_i = y − w(y)`) at incumbent `(x, h)`, the new incumbent is `(M_i, Ĥ_i)` with
`M_i = max {x, X_i}` and `Ĥ_i = h` if `X_i < x`, `max {h, H_i}` if `X_i = x`, `H_i` if
`X_i > x`. -/
def updState (w : ℝ → ℝ) (x h y : ℝ) : ℝ × ℝ :=
  (max x (w y), if w y < x then h else if w y = x then max h (y - w y) else y - w y)

/-- The lexicographic maximum of two (wage, residual) pairs. -/
def lexMax (p q : ℝ × ℝ) : ℝ × ℝ :=
  if p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) then q else p

variable {κ ι : Type*} [DecidableEq ι]

/-- The incumbent after the boxes of `S` have been opened, starting from the pair `p₀`: the
lexicographic maximum of `p₀` and the pairs `(w(y_j), y_j − w(y_j))`, `j ∈ S`. -/
def stateAfter (w : ℝ → ℝ) (p₀ : ℝ × ℝ) (S : Finset ι) (y : ι → ℝ) : ℝ × ℝ :=
  S.toList.foldl (fun p j => lexMax p (w (y j), y j - w (y j))) p₀

/-- The highest available wage after the boxes of `S` have been opened, starting from
wage `x`. -/
def curWage (w : ℝ → ℝ) (x : ℝ) (S : Finset ι) (y : ι → ℝ) : ℝ :=
  S.toList.foldl (fun a j => max a (w (y j))) x

/-- The submitted outcome of a decision, if it stops. -/
def Choice.submitted? {R S : Finset ι} : Choice κ R S → Option (κ ⊕ ι)
  | .openBox _ _ _ => none
  | .stop s => some (s.map id Subtype.val)

variable [Fintype ι]

/-- Weitzman's index policy from an available wage `x` (Lemma B.3, p. 23, and its proof,
p. 33): at every opened set `S`, with current highest available wage `x'` and largest remaining
reservation value `ρ̄ = max_{i ∉ S} ρ_i` (`⊥` if none remain), it opens a box of index `ρ̄`
when `x' < ρ̄`, and otherwise stops and submits an available outcome of wage `x'`. -/
def IsIndexPolicy (w : ℝ → ℝ) (T : ι → Box) (x : ℝ)
    (π : Policy Unit (Finset.univ : Finset ι)) : Prop :=
  ∀ (S : Finset ι) (y : ι → ℝ) (u : ℝ),
    (((curWage w x S y : ℝ) : EReal) < (Finset.univ \ S).sup (fun i => resv w (T i)) →
      ∃ i, (π.rule S y u).box? = some i ∧
        resv w (T i) = (Finset.univ \ S).sup (fun i => resv w (T i))) ∧
    (¬ (((curWage w x S y : ℝ) : EReal) < (Finset.univ \ S).sup (fun i => resv w (T i))) →
      (π.rule S y u).box? = none ∧
        ∀ s, (π.rule S y u).submitted? = some s →
          (match s with
            | Sum.inl _ => x
            | Sum.inr j => w (y j)) = curWage w x S y)

/-- The Bellman agent value of opening box `i` at state `(R, x, h)`:
`u_i = −c_i + E[U(R \ {i}, M_i, Ĥ_i)]` (eq. (17), p. 22). -/
def openU (w : ℝ → ℝ) (T : ι → Box) (R : Finset ι) (x h : ℝ) (i : ι) : EReal :=
  -(((T i).cost : ℝ) : EReal) +
    eexp ((T i).out.law : Measure ℝ) fun y =>
      Ubell w T (R.erase i) (updState w x h y).1 (updState w x h y).2

/-- The Bellman principal value of opening box `i` at state `(R, x, h)`:
`p_i = E[P(R \ {i}, M_i, Ĥ_i)]` (eq. (17), p. 22). -/
def openP (w : ℝ → ℝ) (T : ι → Box) (R : Finset ι) (x h : ℝ) (i : ι) : EReal :=
  eexp ((T i).out.law : Measure ℝ) fun y =>
    Pbell w T (R.erase i) (updState w x h y).1 (updState w x h y).2

/-- A dynamically consistent policy for `V_P(w | A)` (Lemma B.1, p. 22): at every opened set
`S`, with current incumbent `(x_S, h_S)` (the lexicographic maximum of the null pair and the
observed pairs) and unopened set `R = A \ S`, its decision attains the Bellman lexicographic
maximum of (17): an opened box `i` has `u_i = U(R, x_S, h_S)` and `p_i = P(R, x_S, h_S)`;
stopping has `x_S = U(R, x_S, h_S)`, `h_S = P(R, x_S, h_S)` and submits an outcome with pair
`(x_S, h_S)`. -/
def IsDynConsistent (w : ℝ → ℝ) (T : ι → Box)
    (π : Policy Unit (Finset.univ : Finset ι)) : Prop :=
  ∀ (S : Finset ι) (y : ι → ℝ) (u : ℝ),
    (∀ i, (π.rule S y u).box? = some i →
      openU w T (Finset.univ \ S) (stateAfter w (nullPair w ()) S y).1
          (stateAfter w (nullPair w ()) S y).2 i =
        Ubell w T (Finset.univ \ S) (stateAfter w (nullPair w ()) S y).1
          (stateAfter w (nullPair w ()) S y).2 ∧
      openP w T (Finset.univ \ S) (stateAfter w (nullPair w ()) S y).1
          (stateAfter w (nullPair w ()) S y).2 i =
        Pbell w T (Finset.univ \ S) (stateAfter w (nullPair w ()) S y).1
          (stateAfter w (nullPair w ()) S y).2) ∧
    ((π.rule S y u).box? = none →
      (((stateAfter w (nullPair w ()) S y).1 : ℝ) : EReal) =
          Ubell w T (Finset.univ \ S) (stateAfter w (nullPair w ()) S y).1
            (stateAfter w (nullPair w ()) S y).2 ∧
      (((stateAfter w (nullPair w ()) S y).2 : ℝ) : EReal) =
          Pbell w T (Finset.univ \ S) (stateAfter w (nullPair w ()) S y).1
            (stateAfter w (nullPair w ()) S y).2 ∧
      ∀ s, (π.rule S y u).submitted? = some s →
        outcomePair w (nullPair w) y s = stateAfter w (nullPair w ()) S y)

end OneTrap.Core


