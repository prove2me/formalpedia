-- Prove2me | Definitions.Def_MDPFinance_POMDP_FilteredModel
-- name    : MDPFinance_POMDP_FilteredModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:14:37.856356+00:00
-- url     : https://prove2.me/theorems/9aac2d85-1d09-491d-911a-0a4fbb9aacc6
-- title:
--   Definition 5.3.1 — the filtered Markov Decision Model and its value functions
-- statement:
--   $(E,A,D',Q',r',g',\beta)$ with $E:=E_X\times\mathbb{P}(E_Y)$; $D'(x,\rho):=D(x)$;
--   $$Q'(B\times C\mid x,\rho,a) := \int_B \mathbf{1}_C\big(\Phi(x,\rho,a,x')\big)\,
--   Q^X(dx'\mid x,\rho,a), \qquad r'(x,\rho,a):=\int r(x,y,a)\rho(dy), \qquad
--   g'(x,\rho):=\int g(x,y)\rho(dy),$$
--   where $Q^X(\cdot\mid x,\rho,a):=\int Q^X(\cdot\mid x,y,a)\rho(dy)$. Value functions
--   $J_{N\pi}'(x,\rho)$, $J_N'(x,\rho):=\sup_{\pi\in\Pi_N}J_{N\pi}'(x,\rho)$ are defined
--   exactly as in Chapter 2, but — crucially — for the *same* history-dependent policy class
--   $\Pi_N$ as the original POMDP (every $\pi\in\Pi_N$ is a feasible, generally non-Markov,
--   policy for the filtered model too).
--
--   $(x,\rho)$ is a bona fide state of a *standard* Markov Decision Model, to which Chapter 2's
--   whole machinery — in particular Theorem 2.3.8 — now applies directly.
--
--   **Formalization Note.** `Qprime` is carried as data (a genuine kernel into $E_X\times
--   \mathbb{P}(E_Y)$) characterized by `hQprime`, matching `Phi`'s own treatment. `ExPrime`
--   threads the filter $\rho$ forward directly via draws from `Qprime` (which already encodes the
--   Bayes update through `Phi`), rather than recomputing it from the full history via `Fd.mu` at
--   every step — the two agree when starting from $\rho=Q_0$ (Theorem 5.3.2), but `ExPrime`/`Jprime`
--   must accept an *arbitrary* initial $\rho$ for Theorem 5.3.3's Bellman equation to be a
--   meaningful statement about every state $(x,\rho)\in E$, not just states reachable from $Q_0$.
--
--   **Moderation note.** $r'$, $g'$, $T'$, the policy values and $J'_n$ are in $[-\infty,\infty]$ (`erealIntegral`), matching the POMDP side, so that Theorem 5.3.2's equality is between the book's extended-real expectations and not between default values.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 156-157, PDF 170-171, Definition 5.3.1

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy
import Definitions.Def_MDPFinance_POMDP_FilterData
import Definitions.Def_MDPFinance_POMDP_Objective

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

/-- `Q^X(·|x,ρ,a) := ∫ Q^X(·|x,y,a) ρ(dy)`, the marginal law of the next observable state under
filter `ρ` (Bäuerle–Rieder, unnumbered display, p. 158, PDF 172), realized as a `Measure.bind` of
`ρ` against the pushforward-under-`Prod.fst` of `Q`. -/
noncomputable def FilterData.QXprime (M : PartiallyObservableMDM EX EY A) (_Fd : FilterData M)
    (x : EX) (ρ : ProbabilityMeasure EY) (a : A) : Measure EX :=
  ρ.toMeasure.bind fun y => (M.Q ((x, y), a)).map Prod.fst

/-- Definition 5.3.1. The filtered Markov Decision Model `(E,A,D,Q',r',g',β)` (Bäuerle–Rieder,
p. 156, PDF 170): `E := E_X × ℙ(E_Y)`; `D(x,ρ) := D(x)`; `Q'(B×C|x,ρ,a) := ∫_B 1_C(Φ(x,ρ,a,x'))
Q^X(dx'|x,ρ,a)` — realized as the pushforward of `Q^X(·|x,ρ,a)` under `x' ↦ (x',Φ(x,ρ,a,x'))`,
carried as *data* (a genuine kernel into the Borel space `E_X × ℙ(E_Y)`, per this chunk's own
pitfall) characterized by `hQprime`, its defining formula; `r'(x,ρ,a) := ∫ r(x,y,a)ρ(dy)`;
`g'(x,ρ) := ∫ g(x,y)ρ(dy)`. -/
structure FilteredModel (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M) where
  Qprime : Kernel ((EX × ProbabilityMeasure EY) × A) (EX × ProbabilityMeasure EY)
  hQprime : ∀ x (ρ : ProbabilityMeasure EY) a,
    Qprime ((x, ρ), a) = (Fd.QXprime M x ρ a).map fun x' => (x', Fd.Phi x ρ a x')

/-- `D'(x,ρ) := D(x)` (Bäuerle–Rieder, p. 156, PDF 170). -/
def FilteredModel.Dprime (M : PartiallyObservableMDM EX EY A) (e : EX × ProbabilityMeasure EY) :
    Set A :=
  M.Dx e.1

/-- `r'(x,ρ,a) := ∫ r(x,y,a) ρ(dy) ∈ [-∞,∞]` (Bäuerle–Rieder, p. 156, PDF 170), as an
`erealIntegral` so that a one-stage reward without finite expectation is `±∞`, not a default
real. -/
noncomputable def FilteredModel.rprime (M : PartiallyObservableMDM EX EY A)
    (e : EX × ProbabilityMeasure EY) (a : A) : EReal :=
  erealIntegral e.2.toMeasure (fun y => (M.r (e.1, y, a) : EReal))

/-- `g'(x,ρ) := ∫ g(x,y) ρ(dy) ∈ [-∞,∞]` (Bäuerle–Rieder, p. 156, PDF 170). -/
noncomputable def FilteredModel.gprime (M : PartiallyObservableMDM EX EY A)
    (e : EX × ProbabilityMeasure EY) : EReal :=
  erealIntegral e.2.toMeasure (fun y => (M.g (e.1, y) : EReal))

/-- The Bellman (maximal-reward) operator `T'_n v(x,ρ) := sup_{a ∈ D(x)} [r'(x,ρ,a) + β ∫ v(x',ρ')
Q'(d(x',ρ')|x,ρ,a)]` of the filtered model (Bäuerle–Rieder, p. 158, PDF 172), in `[-∞,∞]`. -/
noncomputable def FilteredModel.Tprime (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (v : EX × ProbabilityMeasure EY → EReal)
    (e : EX × ProbabilityMeasure EY) : EReal :=
  ⨆ a ∈ M.Dx e.1, FilteredModel.rprime M e a +
    (M.β : EReal) * erealIntegral (M'.Qprime (e, a)) v

/-- The expectation, under an observable-history-dependent policy `π ∈ Π_N`, of the filtered
model's reward-to-go over `k` more stages from `(x_n,ρ_n) = (xs n, Fd.mu n xs as)` — the filtered
analogue of `PartiallyObservableMDM.Ex`/`Vpi`, used to give `Π_N`-policies (not just Markov ones)
a value under the filtered model, as the book's own `J'_{Nπ}` for `π ∈ Π_N` requires
(Bäuerle–Rieder, p. 157-158, PDF 171-172). -/
noncomputable def FilteredModel.ExPrime (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (π : Policy EX A) :
    (k : ℕ) → (n : ℕ) → (xs : ℕ → EX) → (as : ℕ → A) → (ρ : ProbabilityMeasure EY) → EReal
  | 0, n, xs, _, ρ => FilteredModel.gprime M (xs n, ρ)
  | (k + 1), n, xs, as, ρ =>
      let a := π n xs as
      FilteredModel.rprime M (xs n, ρ) a + (M.β : EReal) *
        erealIntegral (M'.Qprime ((xs n, ρ), a)) (fun e' : EX × ProbabilityMeasure EY =>
          FilteredModel.ExPrime M Fd M' π k (n + 1) (Function.update xs (n + 1) e'.1)
            (Function.update as n a) e'.2)

/-- `J'_{Nπ}(x,ρ)` for `π ∈ Π_N`, from the filtered state `(x,ρ)` (Bäuerle–Rieder, p. 157,
PDF 171). -/
noncomputable def FilteredModel.JprimeNpi (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) [Nonempty A] (π : Policy EX A) (N : ℕ) (x : EX)
    (ρ : ProbabilityMeasure EY) : EReal :=
  FilteredModel.ExPrime M Fd M' π N 0 (fun _ => x) (fun _ => Classical.arbitrary A) ρ

/-- `J'_N(x,ρ) := sup_{π ∈ Π_N} J'_{Nπ}(x,ρ)` (Bäuerle–Rieder, p. 157, PDF 171); more generally
(taking `N` as "stages-to-go") `J'_n(x,ρ) := sup_{π ∈ Π_n} J'_{nπ}(x,ρ)`, matching the book's own
use of `n` as the stages-remaining index in Theorem 5.3.3. -/
noncomputable def FilteredModel.Jprime (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) [Nonempty A] (n : ℕ) (x : EX) (ρ : ProbabilityMeasure EY) :
    EReal :=
  ⨆ π ∈ {π : Policy EX A | M.IsPolicy n π}, FilteredModel.JprimeNpi M Fd M' π n x ρ

end MDPFinance.POMDP


