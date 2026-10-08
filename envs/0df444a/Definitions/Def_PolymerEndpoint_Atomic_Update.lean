-- Prove2me | Definitions.Def_PolymerEndpoint_Atomic_Update
-- name    : PolymerEndpoint_Atomic_Update
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:59.968387+00:00
-- url     : https://prove2.me/theorems/fffc5823-9d03-42e9-896c-03a5943344dc
-- title:
--   Update map, invariant laws, and variational functionals
-- statement:
--   For a partitioned subprobability measure $f$, fresh disorder $Y$, and inverse temperature $\beta$, the update places at site $u$ mass proportional to the sum of neighboring masses of $f$ times $e^{\beta Y_u}$. The denominator adds the contribution $2d(1-\|f\|)e^{\lambda(\beta)}$ from mass escaped to infinity. The law of the updated state is $\mathcal T f$; extending this kernel to a law $\nu$ gives $\mathcal T\nu$. The expected log normalized denominator defines $R(f)$, and its average under $\nu$ defines $\mathcal R(\nu)$.
--
--   The set $\mathcal K$ consists of probability laws fixed by $\mathcal T$; $\mathcal M$ consists of those fixed laws minimizing $\mathcal R$. The empirical law $\mu_n$ averages point masses at the first $n$ endpoint distributions. The Wasserstein distance $\mathcal W$ uses the partitioned-space cost $d$.
--
--   **Formalization Note** The denominator's nonnegative series is summed in extended nonnegative reals before conversion; its finiteness and the update's measurability under the standing assumptions are part of the development. The transport-cost definition is imported from the published platform item. The set $\mathcal M$ uses direct comparison over $\mathcal K$, avoiding a default value for an empty real infimum.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 24, (2.12); pp. 27–29, (3.7)–(3.8); pp. 30–34, (4.1), (4.5)–(4.8)

import Definitions.Def_PolymerEndpoint_Atomic_Partitioned
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

noncomputable def nbr {d : ℕ} (f : PSM d) (Y : Cell d → ℝ)
    (β : ℝ) (u : Cell d) : ℝ :=
  (∑ j : Fin d,
    (f.toFun (u.1, u.2 + Pi.single j 1) +
      f.toFun (u.1, u.2 - Pi.single j 1))) * Real.exp (β * Y u)

noncomputable def Ftil {d : ℕ} (𝔏 : Measure ℝ) (β : ℝ)
    (f : PSM d) (Y : Cell d → ℝ) : ℝ :=
  (∑' u, ENNReal.ofReal (nbr f Y β u)).toReal +
    2 * d * (1 - mass f) * Real.exp (logMGF 𝔏 β)

noncomputable def Fupd {d : ℕ} (𝔏 : Measure ℝ) (β : ℝ)
    (f : PSM d) (Y : Cell d → ℝ) : PSM d :=
  toPSM (fun u => nbr f Y β u / Ftil 𝔏 β f Y)

noncomputable def T {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (β : ℝ) (f : PSM d) : Measure (PSM d) :=
  (envLaw (d := d) 𝔏).map (Fupd 𝔏 β f)

noncomputable def R {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (β : ℝ) (f : PSM d) : ℝ :=
  ∫ Y, Real.log (Ftil 𝔏 β f Y / (2 * d)) ∂(envLaw (d := d) 𝔏)

noncomputable def Tlift {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (β : ℝ) (ν : Measure (PSM d)) : Measure (PSM d) :=
  ν.bind (T 𝔏 β)

noncomputable def W {d : ℕ} (μ ν : Measure (PSM d)) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun f g => ENNReal.ofReal (dist f g)) μ ν

noncomputable def Wdist {d : ℕ} (μ : Measure (PSM d))
    (U : Set (Measure (PSM d))) : ENNReal :=
  ⨅ ν ∈ U, W μ ν

def K {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) :
    Set (Measure (PSM d)) :=
  {ν | IsProbabilityMeasure ν ∧ Tlift 𝔏 β ν = ν}

noncomputable def RR {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (β : ℝ) (ν : Measure (PSM d)) : ℝ :=
  ∫ f, R 𝔏 β f ∂ν

def M {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) :
    Set (Measure (PSM d)) :=
  {ν | ν ∈ K 𝔏 β ∧ ∀ ν' : Measure (PSM d), ν' ∈ K 𝔏 β →
    RR 𝔏 β ν ≤ RR 𝔏 β ν'}

noncomputable def empirical {d : ℕ} {Ω : Type*}
    (X : Cell d → Ω → ℝ) (β : ℝ) (n : ℕ) (a : Ω) : Measure (PSM d) :=
  (n : ENNReal)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (ofPMF (endpt X β i a))

end PolymerEndpoint.Atomic


