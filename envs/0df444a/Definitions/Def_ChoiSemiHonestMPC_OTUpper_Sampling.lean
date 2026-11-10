-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Sampling
-- name    : ChoiSemiHonestMPC_OTUpper_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:28:18.575206+00:00
-- url     : https://prove2.me/theorems/0194c705-f83b-4128-aaba-f25528a0d8f8
-- title:
--   Revelation-flag samplers and the hidden-half experiment (Section 4.1)
-- statement:
--   Objects for Lemmas 4.1–4.3. `bitLaw` is a uniform bit and `bernLaw p` a Bernoulli($p$) flag, both as measures. A sampler receives `Info`, the flag $f$ and the bit $f\wedge B$, which equals $B$ when the flag is set and carries nothing otherwise (`revealMap`). `flagSamplerLaw μI p η` is the joint law of $(\mathrm{Info},B,\mathrm{View}')$ when $\mathrm{Info}\sim\mu_I$, $B$ is an independent uniform bit, the flag an independent Bernoulli($p$), and $\mathrm{View}'\sim\eta(\mathrm{Info},f,f\wedge B)$. `seqViewLaw μI κD μs k` is the joint law of $((\mathrm{Info},B_1..B_K,D),(\mathrm{View}_1..\mathrm{View}_K))$ generated sequentially: $\mathrm{Info}\sim\mu_I$, $D\sim\kappa_D(\mathrm{Info})$, independent uniform bits, then $\mathrm{View}_i\sim\mu_i(\mathrm{Info},D,\mathrm{View}_{<i},B_i)$ for $i=1,2,\dots$, stopped after $k$ views (coordinates not yet generated hold a fixed arbitrary value). `revealVec` gives a sequential sampler the flags and flag-revealed bits. `hiddenHalfLaw m t C_b` is $\mathcal L(\mathrm{View}\mid B=b)$ of Lemma 4.3: $J$ uniform on the half $C_b$, an independent uniform $t$-subset $E$ of $\{0,\dots,m-1\}$, and $\mathrm{View}=(E,Z)$ with $Z=J$ if $J\in E$ and $Z=\bot$ otherwise.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Section 4.1 (Lemmas 4.1–4.3), p. 15–16 (PDF 17–18)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Prob

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-! ### Section 4.1: revelation flags (general measurable spaces) -/

/-- Law of a uniform bit. -/
def bitLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- Law of a Bernoulli(`p`) flag. -/
def bernLaw (p : ℝ) : Measure Bool := (bern p).toMeasure

/-- What a sampler receives besides `Info`: the flag `f` and, only when `f` is set, the
hidden bit `B` (encoded as `(f, f && B)`). -/
def revealMap {I : Type*} : (I × Bool) × Bool → I × Bool × Bool :=
  fun x => (x.1.1, x.2, x.2 && x.1.2)

lemma measurable_revealMap {I : Type*} [MeasurableSpace I] :
    Measurable (revealMap : (I × Bool) × Bool → I × Bool × Bool) := by
  have hg : Measurable (fun y : Bool × Bool => y.2 && y.1) := measurable_of_countable _
  exact measurable_fst.fst.prodMk
    (measurable_snd.prodMk (hg.comp (measurable_fst.snd.prodMk measurable_snd)))

/-- Forget the flag. -/
def dropFlag {I V : Type*} : ((I × Bool) × Bool) × V → (I × Bool) × V :=
  fun x => (x.1.1, x.2)

lemma measurable_dropFlag {I V : Type*} [MeasurableSpace I] [MeasurableSpace V] :
    Measurable (dropFlag : ((I × Bool) × Bool) × V → (I × Bool) × V) :=
  measurable_fst.fst.prodMk measurable_snd

/-- Joint law of `(Info, B, View')` when `Info ~ μI`, `B` is an independent uniform bit,
the flag is an independent Bernoulli(`p`), and `View'` is produced by the sampler `η` from
`Info` and the flag-revealed bit. -/
def flagSamplerLaw {I V : Type*} [MeasurableSpace I] [MeasurableSpace V] (μI : Measure I)
    (p : ℝ) (η : Kernel (I × Bool × Bool) V) [IsMarkovKernel η] : Measure ((I × Bool) × V) :=
  (((μI.prod bitLaw).prod (bernLaw p)) ⊗ₘ (η.comap revealMap measurable_revealMap)).map dropFlag

/-! ### Lemma 4.2: sequential flags (general measurable spaces) -/

/-- Law of `K` independent uniform bits. -/
def bitsLaw (K : ℕ) : Measure (Fin K → Bool) := Measure.pi fun _ => bitLaw

/-- Law of `K` independent Bernoulli(`p`) flags. -/
def flagsLaw (K : ℕ) (p : ℝ) : Measure (Fin K → Bool) := Measure.pi fun _ => bernLaw p

/-- `(B, f) ↦ (f, f && B)`. -/
def maskPair : Bool × Bool → Bool × Bool := fun y => (y.2, y.2 && y.1)

/-- What the sequential sampler receives: for each `i`, the flag and the flag-revealed
hidden bit `B_i`. -/
def revealVec {I : Type*} {K : ℕ} : (I × (Fin K → Bool)) × (Fin K → Bool) →
    I × (Fin K → Bool × Bool) :=
  fun x => (x.1.1, fun i => maskPair (x.1.2 i, x.2 i))

lemma measurable_revealVec {I : Type*} [MeasurableSpace I] {K : ℕ} :
    Measurable (revealVec : (I × (Fin K → Bool)) × (Fin K → Bool) →
      I × (Fin K → Bool × Bool)) := by
  refine measurable_fst.fst.prodMk (measurable_pi_lambda _ fun i => ?_)
  have hg : Measurable maskPair := measurable_of_countable _
  exact hg.comp (((measurable_pi_apply i).comp measurable_fst.snd).prodMk
    ((measurable_pi_apply i).comp measurable_snd))

/-- One step of the sequential view generation: given `((Info, B, D), views)`, draw
`View_i ~ μ_i(Info, D, views, B_i)` and store it in coordinate `i`. -/
def viewStep {I D V : Type*} [MeasurableSpace I] [MeasurableSpace D] [MeasurableSpace V]
    {K : ℕ} (μs : Fin K → Kernel (I × D × (Fin K → V) × Bool) V) [∀ i, IsMarkovKernel (μs i)]
    (i : Fin K) :
    Kernel ((I × (Fin K → Bool) × D) × (Fin K → V)) ((I × (Fin K → Bool) × D) × (Fin K → V)) :=
  ((Kernel.deterministic id measurable_id) ×ₖ
      ((μs i).comap (fun y : (I × (Fin K → Bool) × D) × (Fin K → V) =>
          (y.1.1, y.1.2.2, y.2, y.1.2.1 i))
        (measurable_fst.fst.prodMk (measurable_fst.snd.snd.prodMk
          (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst.snd.fst)))))).map
    (fun z => (z.1.1, Function.update z.1.2 i z.2))

/-- The joint law of `((Info, B_1..B_K, D), (View_1, …, View_K))` generated sequentially:
`Info ~ μI`, `D ~ κD(Info)`, independent uniform bits `B`, then `View_1, View_2, …` in
order, `View_i ~ μ_i(Info, D, View_{<i}, B_i)`; `seqViewLaw … k` stops after `k` views
(coordinates not yet generated hold an arbitrary fixed value). -/
def seqViewLaw {I D V : Type*} [MeasurableSpace I] [MeasurableSpace D] [MeasurableSpace V]
    [Nonempty V] {K : ℕ} (μI : Measure I) (κD : Kernel I D) [IsMarkovKernel κD]
    (μs : Fin K → Kernel (I × D × (Fin K → V) × Bool) V) [∀ i, IsMarkovKernel (μs i)]
    (k : ℕ) : Measure ((I × (Fin K → Bool) × D) × (Fin K → V)) :=
  ((List.finRange K).take k).foldl (fun m i => m.bind (viewStep μs i))
    (((μI ⊗ₘ κD).prod (bitsLaw K)).map
      (fun x => ((x.1.1, x.2, x.1.2), fun _ => Classical.arbitrary V)))

/-! ### Lemma 4.3: the hidden-half experiment (finite) -/

/-- `L(View | B = b)` in Lemma 4.3: `J` uniform on the half `C_b`, an independent uniform
`t`-subset `E` of the pool `{0, …, m-1}`, and `View = (E, Z)` with `Z = J` if `J ∈ E`
and `Z = ⊥` (`none`) otherwise. -/
def hiddenHalfLaw (m t : ℕ) (Cb : Finset (Fin m)) : PMF (Finset (Fin m) × Option (Fin m)) :=
  if h : Cb.Nonempty then
    (PMF.uniformOfFinset Cb h).bind fun J =>
      (unifSubsets Finset.univ t).map fun E => (E, if J ∈ E then some J else none)
  else PMF.pure (∅, none)

end ChoiSemiHonestMPC.OTUpper


