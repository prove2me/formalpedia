-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_Zones__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:49:00.694502+00:00
-- url     : https://prove2.me/theorems/b65c2e1d-abf9-4daf-91da-096f60e37310
-- title:
--   Slices of subsets of $E_0$, the upper and lower zones of a rank model, and admissible sets between them
-- statement:
--   Notation follows the earlier definitions. $D$ is the countable set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, with finite blocks $D_m=\{(m,g)\}$ of size $2^{2^m}$, and $E_0=D\times\{0,1\}$ has blocks $W_m=D_m\times\{0,1\}$. For $X\subseteq E_0$ put $\delta_m(X)=|X\cap W_m|/|W_m|$; $X$ is *small* if $\delta_m(X)\to0$. For $u\subseteq D$ put $\delta^D_m(u)=|u\cap D_m|/|D_m|$; $u$ has *density zero* if $\delta^D_m(u)\to0$. Let $\mathcal C$ be the well-ordered index set of cardinality $2^{\aleph_0}$ used throughout the construction. $\mathcal K$ is the column ideal on $D$: $u$ is $\mathcal K$-small if $u\cap\bigcap_{t\in F}A_t$ has density zero for some finite $F\subseteq\mathcal C$, where the $A_t$ are the $A$-columns and the empty intersection is $D$. The sets $H_{t,k}\subseteq E_0$ ($t\in\mathcal C$, $k\in\{0,1\}$) are the reservation cells. Complements of subsets of $D$ are taken in $D$, complements of subsets of $E_0$ in $E_0$.
--
--   A *rank model* $R$ on $D$ consists of a proper ideal $\mathcal J$ of subsets of $D$, an ultrafilter $\mathcal U$ on $D$ containing no member of $\mathcal J$, and a rank $\rho$ assigning to every subset of $D$ an element of $\mathcal C$, such that $\rho(Y)\le\rho(X)$ whenever $X,Y\in\mathcal U$ and $X\setminus Y\in\mathcal J$, and such that the thinning property holds: if $s\subseteq X$, $s\notin\mathcal U$, $X\in\mathcal U$ and $\gamma\in\mathcal C$, then some $u\in\mathcal U$ has $s\subseteq u\subseteq X$ and $\gamma<\rho(u)$. Fix such an $R$.
--
--   1. **Slices.** For $X\subseteq E_0$ and $b\in\{0,1\}$, $X_b=\{d\in D:\ (d,b)\in X\}$. Slicing commutes with complements and symmetric differences, $\emptyset_b=\emptyset$, $(E_0)_b=D$, and $X\subseteq Y$ holds if and only if $X_0\subseteq Y_0$ and $X_1\subseteq Y_1$.
--   2. **Joining slices.** For $u,v\subseteq D$, $\mathrm{join}(u,v)=(u\times\{0\})\cup(v\times\{1\})\subseteq E_0$; its slices are $\mathrm{join}(u,v)_0=u$ and $\mathrm{join}(u,v)_1=v$.
--   3. **Doubly $\mathcal K$-small sets.** $X\subseteq E_0$ is doubly $\mathcal K$-small if both slices $X_0$ and $X_1$ are $\mathcal K$-small.
--   4. **Admissible sets.** $X\subseteq E_0$ is $R$-admissible if
--   $$\bigl(X_0\in\mathcal U,\ X_1^c\in\mathcal U,\ \rho(X_1^c)<\rho(X_0)\bigr)\quad\text{or}\quad\bigl(X_0\notin\mathcal U,\ X_1^c\notin\mathcal U,\ \rho(X_1)<\rho(X_0^c)\bigr).$$
--   5. **Upper and lower sets.** $X\subseteq E_0$ is *upper* if $X_0\in\mathcal U$ and either $X_1^c\notin\mathcal U$, or $X_1^c\in\mathcal U$ and $\rho(X_0)\le\rho(X_1^c)$. It is *lower* if $X^c$ is upper; explicitly, $X_0^c\in\mathcal U$ and either $X_1\notin\mathcal U$, or $X_1\in\mathcal U$ and $\rho(X_0^c)\le\rho(X_1)$.
--
--   The file proves the following facts.
--
--   - *Slice densities.* $\delta^D_m(X_b)\le2\,\delta_m(X)$ for every $X\subseteq E_0$, $b\in\{0,1\}$ and $m\in\mathbb N$. Consequently both slices of a small set have density zero, every small set is doubly $\mathcal K$-small, subsets of doubly $\mathcal K$-small sets are doubly $\mathcal K$-small, and every reservation cell $H_{t,k}$ is doubly $\mathcal K$-small.
--   - *Trichotomy.* $X$ is admissible if and only if it is neither upper nor lower; no upper set is lower; the complement of an admissible set is admissible; $\emptyset$ is not upper and $E_0$ is not lower.
--   - *Monotonicity.* If $X$ is upper and $X\subseteq Y$, then $Y$ is upper; if $Y$ is lower and $X\subseteq Y$, then $X$ is lower.
--   - *Invariance.* Assume $\mathcal J=\mathcal K$. If $X\triangle Y$ is doubly $\mathcal K$-small, then $X$ is upper if and only if $Y$ is upper, $X$ is lower if and only if $Y$ is lower, and $X$ is admissible if and only if $Y$ is admissible. Moreover, under the same assumption no admissible set is small.
--   - *Zone crossing.* If $A\subseteq Z\subseteq E_0$, $A$ is lower and $Z$ is upper, then some admissible $B$ satisfies $A\subseteq B\subseteq Z$.
--   - *Admissible sets between the zones.* If $A\subseteq Z\subseteq E_0$, $A$ is not upper and $Z$ is not lower, then there is an $R$-admissible set $B$ with
--   $$A\subseteq B\subseteq Z .$$
--
--   Admissible sets are the sets allowed as prototype sets in the construction of the self-dual matroid on $E_0$. The upper sets form an up-set and the lower sets a down-set of the power set of $E_0$, the two zones are disjoint and exchanged by complementation, and the admissible sets are exactly the sets lying in neither zone; the last fact turns this into an existence statement for every interval running from outside the upper zone to outside the lower zone. Invariance under doubly $\mathcal K$-small changes, which include changes by small sets and changes inside reservation cells, allows the endpoints of such an interval to be modified without changing their status; this is what makes room for inserting a new admissible prototype with prescribed separation properties.
--
--   **Formalization Note** Bits are `Bool` (`false` is $0$, `true` is $1$), and $\mathcal C$ is the type `CIndex`. The definitions are `slice X b`, `joinSlices u v` (the set `{x | if x.2 then x.1 ∈ v else x.1 ∈ u}`), `KSmall0` (doubly $\mathcal K$-small) and, for `R : RankModel D`, the predicates `R.Admissible`, `R.Upper` and `R.Lower` (the last defined as `R.Upper Xᶜ`). The slice-density bound `density_slice_le` compares `dDensity` (density in $D_m$) with `density` (density in $W_m$), using $|W_m|=2|D_m|$. `status_invariant` and `admissible_positive` assume `R.ideal = KIdeal`; all other statements hold for an arbitrary rank model on $D$. The remaining lemmas are `slice_compl`, `slice_symmDiff`, `slice_empty`, `slice_univ`, `slice_mono`, `subset_iff_slice`, `slice_join_false`, `slice_join_true`, `small_slice`, `small_kSmall0`, `kSmall0_mono`, `hCell_kSmall0`, `admissible_iff`, `admissible_compl`, `upper_mono`, `lower_mono`, `upper_not_lower`, `not_upper_empty`, `not_lower_univ`, `zone_crossing` and `exists_admissible_between`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Zones.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Zones.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension__InfiniteMatroidCorollaries

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

def slice (X : Set E0) (b : Bool) : Set D := {d | (d,b) ∈ X}
@[simp] lemma slice_compl (X : Set E0) (b : Bool) : slice Xᶜ b = (slice X b)ᶜ := rfl
@[simp] lemma slice_symmDiff (X Y : Set E0) (b : Bool) : slice (X ∆ Y) b = slice X b ∆ slice Y b := rfl
@[simp] lemma slice_empty (b : Bool) : slice ∅ b = ∅ := rfl
@[simp] lemma slice_univ (b : Bool) : slice univ b = univ := rfl
lemma slice_mono {X Y : Set E0} (h : X ⊆ Y) (b : Bool) : slice X b ⊆ slice Y b := fun _ hx ↦ h hx
lemma subset_iff_slice {X Y : Set E0} : X ⊆ Y ↔ ∀ b, slice X b ⊆ slice Y b := by
  constructor
  · exact slice_mono
  · intro h x hx; exact h x.2 hx

def joinSlices (u v : Set D) : Set E0 := {x | if x.2 then x.1 ∈ v else x.1 ∈ u}
@[simp] lemma slice_join_false (u v : Set D) : slice (joinSlices u v) false = u := by ext; simp [slice,joinSlices]
@[simp] lemma slice_join_true (u v : Set D) : slice (joinSlices u v) true = v := by ext; simp [slice,joinSlices]

lemma density_slice_le (X : Set E0) (b : Bool) (m : ℕ) : dDensity (slice X b) m ≤ 2 * density X m := by
  classical
  have hi : Function.Injective (fun d : D ↦ (d,b)) := fun _ _ h ↦ congrArg Prod.fst h
  have hs : (traceFinset (dBlock m) (slice X b)).image (fun d ↦ (d,b)) ⊆ traceFinset (wBlock m) X := by
    intro x hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdm,hdX⟩ := (mem_traceFinset _ _ _).mp hd
    exact (mem_traceFinset _ _ _).mpr ⟨Finset.mem_product.mpr ⟨hdm,Finset.mem_univ _⟩,hdX⟩
  have hc : ((traceFinset (dBlock m) (slice X b)).card : ℝ) ≤ (traceFinset (wBlock m) X).card := by
    exact_mod_cast ((Finset.card_image_of_injective _ hi) ▸ Finset.card_le_card hs)
  have hw : (0:ℝ) < 2 ^ (2 ^ m) := by positivity
  unfold dDensity density finiteDensity
  rw [card_dBlock,card_wBlock]
  push_cast
  have he (a : ℝ) : 2 * (a / (2 * 2 ^ (2 ^ m))) = a / 2 ^ (2 ^ m) := by ring
  rw [he]
  exact div_le_div_of_nonneg_right hc hw.le

lemma small_slice {X : Set E0} (h : Small X) (b : Bool) : DSmall (slice X b) := by
  have ht : Tendsto (fun m ↦ 2 * density X m) atTop (𝓝 0) := by simpa using h.const_mul 2
  exact squeeze_zero (fun m ↦ finiteDensity_nonneg _ _) (density_slice_le X b) ht

def KSmall0 (X : Set E0) : Prop := ∀ b, KSmall (slice X b)
lemma small_kSmall0 {X : Set E0} (h : Small X) : KSmall0 X := fun b ↦ dSmall_kSmall (small_slice h b)
lemma kSmall0_mono {X Y : Set E0} (hY : KSmall0 Y) (hXY : X ⊆ Y) : KSmall0 X :=
  fun b ↦ kSmall_mono (hY b) (slice_mono hXY b)
lemma hCell_kSmall0 (t : CIndex) (k : Bool) : KSmall0 (HCell t k) := by
  intro b
  exact kSmall_mono (AColumn_compl_kSmall t) (dCell_subset_Acompl t k)

namespace RankModel
variable (R : RankModel D)

def Admissible (X : Set E0) : Prop :=
  (slice X false ∈ R.ultra ∧ (slice X true)ᶜ ∈ R.ultra ∧
    R.rank (slice X true)ᶜ < R.rank (slice X false)) ∨
  (slice X false ∉ R.ultra ∧ (slice X true)ᶜ ∉ R.ultra ∧
    R.rank (slice X true) < R.rank (slice X false)ᶜ)
def Upper (X : Set E0) : Prop :=
  slice X false ∈ R.ultra ∧ ((slice X true)ᶜ ∉ R.ultra ∨
    ((slice X true)ᶜ ∈ R.ultra ∧ R.rank (slice X false) ≤ R.rank (slice X true)ᶜ))
def Lower (X : Set E0) : Prop := R.Upper Xᶜ

lemma admissible_iff (X : Set E0) : R.Admissible X ↔ ¬ R.Upper X ∧ ¬ R.Lower X := by
  by_cases hu : slice X false ∈ R.ultra <;> by_cases hy : (slice X true)ᶜ ∈ R.ultra <;>
    simp_all [Admissible,Upper,Lower,Ultrafilter.compl_mem_iff_notMem,not_le]

lemma admissible_compl {X : Set E0} (h : R.Admissible X) : R.Admissible Xᶜ := by
  rw [R.admissible_iff] at h ⊢
  simpa only [Lower,compl_compl,and_comm] using h

lemma upper_mono {X Y : Set E0} (hX : R.Upper X) (hXY : X ⊆ Y) : R.Upper Y := by
  have hu : slice Y false ∈ R.ultra := mem_of_superset hX.1 (slice_mono hXY false)
  refine ⟨hu,?_⟩
  by_cases hy : (slice Y true)ᶜ ∈ R.ultra
  · have hyX : (slice X true)ᶜ ∈ R.ultra := mem_of_superset hy (compl_subset_compl.mpr (slice_mono hXY true))
    have hr := hX.2.resolve_left (not_not.mpr hyX)
    refine Or.inr ⟨hy,?_⟩
    exact (R.antitone hX.1 hu (R.ideal.modSubset_of_subset (slice_mono hXY false))).trans
      ((hr.2).trans (R.antitone hy hyX (R.ideal.modSubset_of_subset (compl_subset_compl.mpr (slice_mono hXY true)))))
  · exact Or.inl hy

lemma lower_mono {X Y : Set E0} (hY : R.Lower Y) (hXY : X ⊆ Y) : R.Lower X :=
  R.upper_mono hY (compl_subset_compl.mpr hXY)

lemma upper_not_lower {X : Set E0} (hX : R.Upper X) : ¬ R.Lower X := by
  intro hL
  have hu : (slice X false)ᶜ ∈ R.ultra := hL.1
  exact (Ultrafilter.compl_mem_iff_notMem.mp hu) hX.1
lemma not_upper_empty : ¬ R.Upper ∅ := by simp [Upper]
lemma not_lower_univ : ¬ R.Lower univ := by simpa [Lower] using R.not_upper_empty

variable (hK : R.ideal = KIdeal)
include hK
lemma status_invariant {X Y : Set E0} (h : KSmall0 (X ∆ Y)) :
    (R.Upper X ↔ R.Upper Y) ∧ (R.Lower X ↔ R.Lower Y) ∧
      (R.Admissible X ↔ R.Admissible Y) := by
  have hu : R.ideal.small (slice X false ∆ slice Y false) := by rw [hK]; exact h false
  have hv : R.ideal.small (slice X true ∆ slice Y true) := by rw [hK]; exact h true
  have huc : R.ideal.small ((slice X false)ᶜ ∆ (slice Y false)ᶜ) := by
    convert hu using 1
    ext x; simp only [Set.mem_symmDiff,Set.mem_compl_iff]; tauto
  have hvc : R.ideal.small ((slice X true)ᶜ ∆ (slice Y true)ᶜ) := by
    convert hv using 1
    ext x; simp only [Set.mem_symmDiff,Set.mem_compl_iff]; tauto
  obtain ⟨heu,hru⟩ := R.invariant hu
  obtain ⟨hev,hrv⟩ := R.invariant hv
  obtain ⟨heuc,hruc⟩ := R.invariant huc
  obtain ⟨hevc,hrvc⟩ := R.invariant hvc
  have hUp : R.Upper X ↔ R.Upper Y := by
    constructor
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heu.mp hu,Or.inl (fun hy ↦ hv (hevc.mpr hy))⟩
      · exact ⟨heu.mp hu,Or.inr ⟨hevc.mp hv,by rwa [← hru hu,← hrvc hv]⟩⟩
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heu.mpr hu,Or.inl (fun hx ↦ hv (hevc.mp hx))⟩
      · exact ⟨heu.mpr hu,Or.inr ⟨hevc.mpr hv,by rwa [hru (heu.mpr hu),hrvc (hevc.mpr hv)]⟩⟩
  have hLo : R.Lower X ↔ R.Lower Y := by
    simp only [Lower,Upper,slice_compl,compl_compl]
    constructor
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heuc.mp hu,Or.inl (fun hy ↦ hv (hev.mpr hy))⟩
      · exact ⟨heuc.mp hu,Or.inr ⟨hev.mp hv,by rwa [← hruc hu,← hrv hv]⟩⟩
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heuc.mpr hu,Or.inl (fun hx ↦ hv (hev.mp hx))⟩
      · exact ⟨heuc.mpr hu,Or.inr ⟨hev.mpr hv,by rwa [hruc (heuc.mpr hu),hrv (hev.mpr hv)]⟩⟩
  exact ⟨hUp,hLo,by rw [R.admissible_iff,R.admissible_iff,hUp,hLo]⟩

lemma admissible_positive {X : Set E0} (hX : R.Admissible X) : ¬ Small X := by
  intro hs
  have hl (b : Bool) : slice X b ∉ R.ultra := R.avoids _ (by rw [hK]; exact small_kSmall0 hs b)
  rcases hX with ⟨hu,_,_⟩ | ⟨_,hy,_⟩
  · exact hl false hu
  · exact hy (Ultrafilter.compl_mem_iff_notMem.mpr (hl true))

end RankModel
namespace RankModel
variable (R : RankModel D)

lemma zone_crossing {A Z : Set E0} (hAZ : A ⊆ Z) (hA : R.Lower A) (hZ : R.Upper Z) :
    ∃ B, A ⊆ B ∧ B ⊆ Z ∧ R.Admissible B := by
  have hs : slice A false ∉ R.ultra := Ultrafilter.compl_mem_iff_notMem.mp hA.1
  have hX : slice Z false ∈ R.ultra := hZ.1
  have hsX := slice_mono hAZ false
  by_cases hy : (slice A true)ᶜ ∈ R.ultra
  · obtain ⟨u,hsu,huX,hu,hru⟩ := R.thinning _ _ hsX hs hX (R.rank (slice A true)ᶜ)
    refine ⟨joinSlices u (slice A true),?_,?_,Or.inl ?_⟩
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using hsu
      · simp
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using huX
      · simpa using slice_mono hAZ true
    · simpa only [slice_join_false,slice_join_true] using And.intro hu (And.intro hy hru)
  · have hs' : (slice Z false)ᶜ ∉ R.ultra := fun h ↦ (Ultrafilter.compl_mem_iff_notMem.mp h) hX
    have hX' : (slice A false)ᶜ ∈ R.ultra := Ultrafilter.compl_mem_iff_notMem.mpr hs
    obtain ⟨v,hZv,hvA,hv,hrv⟩ := R.thinning _ _ (compl_subset_compl.mpr hsX) hs' hX'
      (R.rank (slice A true))
    refine ⟨joinSlices vᶜ (slice A true),?_,?_,Or.inr ?_⟩
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using compl_subset_compl.mpr hvA
      · simp
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using compl_subset_compl.mpr hZv
      · simpa using slice_mono hAZ true
    · have hvc : vᶜ ∉ R.ultra := fun h ↦ (Ultrafilter.compl_mem_iff_notMem.mp h) hv
      simpa only [slice_join_false,slice_join_true,compl_compl] using And.intro hvc (And.intro hy hrv)

lemma exists_admissible_between {A Z : Set E0} (hAZ : A ⊆ Z) (hA : ¬ R.Upper A) (hZ : ¬ R.Lower Z) :
    ∃ B, A ⊆ B ∧ B ⊆ Z ∧ R.Admissible B := by
  by_cases ha : R.Admissible A
  · exact ⟨A,Subset.rfl,hAZ,ha⟩
  by_cases hz : R.Admissible Z
  · exact ⟨Z,hAZ,Subset.rfl,hz⟩
  have hAL : R.Lower A := by
    by_contra h
    exact ha ((R.admissible_iff A).mpr ⟨hA,h⟩)
  have hZU : R.Upper Z := by
    by_contra h
    exact hz ((R.admissible_iff Z).mpr ⟨h,hZ⟩)
  exact R.zone_crossing hAZ hAL hZU

end RankModel
end InfiniteMatroidCounterexample
end

end OAI


