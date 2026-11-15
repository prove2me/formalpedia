-- Prove2me | Definitions.Def_Transport_PhysicalHigh_PositiveFineSourceInput
-- name    : Transport_PhysicalHigh_PositiveFineSourceInput
-- status  : Definition
-- author  : @Himan
-- created : 2026-11-15T04:24:28.987081+00:00
-- url     : https://prove2.me/theorems/87258242-dc9d-4c8d-b162-100a5c914f25
-- title:
--   The positive fine source energy input at $\kappa=3/4$ with $N$ slots and loss $\varepsilon_m$
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$).
--
--   This file defines the *positive fine source input*, the hypothesis on arithmetic energies that feeds the marked plain moment of the high-side estimate in LW56e2's refinement.
--
--   **Definition.** Let $F$ be source data with modulus $\mathfrak m$ and Schwartz weight $W$, let $N$ be a number of slots, and let $\varepsilon_m$ and $\mathrm{mesh}$ be real numbers. Put $Q_F=\mathfrak m\cap(72)$. The predicate $\mathrm{PFSI}(F,N,\varepsilon_m,\mathrm{mesh})$ holds when for every $b_\Phi>0$ there are a degree $d\in\mathbb N$ and a finite set $\Sigma$ of Schwartz seminorm indices such that for every Hecke character $\eta_0$ there is $C>0$ for which, for all sufficiently large $U$, the positive energy bound
--   $$
--   \mathcal E\ \le\ C\cdot\mathrm{diag}(\text{radial profile})\cdot\|p\|_\Sigma^{2}\cdot(1+|t|+\mathrm{height})^{d}\cdot U^{\,\mathrm{width}+\varepsilon_m/4}
--   $$
--   holds for every natural energy state at scale $U$ with fixed modulus $Q_F\cap\mathfrak f(\eta_0)$ and width at most $2$, every pair of profiles $p$ supported in $[\tfrac14,\tfrac94]$, every finite family of slots indexed by a subset of $\{1,\dots,N\}$ with widths $w_i\in[0,\mathrm{mesh}]$ and real parts $\sigma_i=\tfrac{33}{50}$, ray characters modulo $(\mathfrak m,\top)$ and heights $|v_i|\le\mathrm{height}$, and all lengths $X_1,X_2\in(0,U]$ subject to the width constraint
--   $$
--   \operatorname{len}_U(X_1)+\operatorname{len}_U(X_2)+6\kappa\sum_iw_i\le\mathrm{width},\qquad\kappa=\tfrac34 .
--   $$
--   Here $\mathcal E$ is the energy of the state against the prime pools at scales $U^{w_i}$ with slot window $\overline W$ and annular weights, in the sense of OpenAI's `CenteredMomentEnergyBands.PositiveAt`.
--
--   **Role.** OpenAI's original predicate of the same name fixes the number of slots, the stage error and $\kappa$ through its geometric data. LW56e2's version takes the number of slots $N$ and the loss $\varepsilon_m$ as arguments and fixes $\kappa=\tfrac34$ and stage error $\varepsilon_m/4$, so that the slot family can be chosen after the geometry. It is the first conjunct of the conclusion of `actual_plain_inputs` and of the hypothesis of `actual_source_moments_from_inputs`.
--
--   **Formalization Note** The predicate is `RH.Transport.PhysicalHigh.PositiveFineSourceInput S N εm mesh`, which unfolds to `PositiveAt (α := Fin N) S.modulus ⊤ le_top (conj ∘ S.W) 2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 (εm/4) (3/4) U η₀ (sourceFixedIdeal S) degree seminorms C`. The arguments are, in order: slot window, slot upper bound $2$, profile support $[\tfrac14,\tfrac94]$, $b_\Phi$, mask bound $0$, length exponent $1$, slot width cap, the interval $[\tfrac{33}{50},\tfrac{33}{50}]$ for $\sigma_i$, width cap $2$, error $\varepsilon_m/4$, $\kappa=\tfrac34$, scale $U$.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/PlainMarked.lean, def PositiveFineSourceInput (L32-L37): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/PlainMarked.lean#L32-L37

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

set_option autoImplicit false

namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

open OAI OAI.SevenEighths
open HeckeFamily ProbeHighRowFamily ProbeFinalAssembly
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource

/-- The positive arithmetic energy input at fixed kappa = 3/4 for a batch of `N`
independent slots, with stage error `εm/4` and mesh `mesh`. -/
def PositiveFineSourceInput {Δ:ℝ}{D:Parameters.HighData Δ}(S:SourceData D)(N:ℕ)(εm mesh:ℝ):Prop:=
  ∀bΦ:ℝ,0<bΦ→∃degree:ℕ,∃seminorms:Finset (ℕ×ℕ),
    ∀η₀:Character,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      PositiveAt (α:=Fin N) S.modulus ⊤ le_top (fun x=>conj (S.W x))
        2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 (εm/4)
        (3/4) U η₀ (sourceFixedIdeal S) degree seminorms C

end
end RH.Transport.PhysicalHigh


