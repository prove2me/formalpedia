-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_LocalBases__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:37:03.268614+00:00
-- url     : https://prove2.me/theorems/8875ba43-3498-49fb-8257-4acd0016f82b
-- title:
--   Labelled probes, the lower local rule, and probe interpolation inside a density class
-- statement:
--   Notation follows the block-density definitions: $D$ is the set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, $E_0=D\times\{0,1\}$, $W_m\subseteq E_0$ is the $m$-th block of elements $((m,g),b)$, $P_n=W_0\cup\dots\cup W_{n-1}$, $\delta_m(X)=|X\cap W_m|/|W_m|$, a set is *small* if $\delta_m(X)\to0$, and $X$ lies in the *class* of $T$ if $X\triangle T$ is small. With $d^T_m(X)=\delta_m(X)-\delta_m(T)$, the probe of $X\subseteq E_0$ relative to $T\subseteq E_0$ is
--
--   $$
--   \phi^T_n(X)=\bigl(|X\cap P_n|-|T\cap P_n|\bigr)+|P_n|\Bigl(\sup_{m\ge n}d^T_m(X)+\inf_{m\ge n}d^T_m(X)\Bigr),
--   $$
--
--   and $\underline\phi^{\,T}(X)=\liminf_{n\to\infty}\phi^T_n(X)\in[-\infty,+\infty]$ is its lower limit.
--
--   1. **Countable ground set.** $D$ and $E_0$ are countably infinite.
--   2. **Labelling.** $\lambda:E_0\to\mathbb N$ is a fixed bijection (chosen non-constructively); for $X\subseteq E_0$ write $\lambda(X)=\{\lambda(x):x\in X\}$.
--   3. **Probe on labels.** For $T\subseteq E_0$, $n\in\mathbb N$ and $A\subseteq\mathbb N$,
--   $$\psi^T_n(A)=\phi^T_n\bigl(\lambda^{-1}(A)\bigr),$$
--   the probe transported to subsets of $\mathbb N$.
--   4. **Lower local rule.** For $T\subseteq E_0$,
--   $$\mathcal L_0(T)=\bigl\{X\subseteq E_0:\ X\triangle T\ \text{is small and}\ -1<\underline\phi^{\,T}(X)\le0\bigr\}.$$
--
--   The file establishes two properties of the transported probe. If $I$ and $Y$ lie in the class of $T$, then $\psi^T$ is cylinder-continuous on the interval $[\lambda(I),\lambda(Y)]$: for every $j$ and every $\varepsilon>0$ there is $m$ such that any two sets $A,A'$ in the interval containing the same labels below $m$ satisfy $|\psi^T_n(A)-\psi^T_n(A')|<\varepsilon$ for all $n<j$. For every $T$, $\psi^T$ has the finite shift property on every interval: $\liminf_n\psi^T_n(B)=\liminf_n\psi^T_n(A)+|B\setminus A|$ whenever $A\subseteq B\subseteq\mathbb N$ and $B\setminus A$ is finite. With these, it proves the probe interpolation theorem.
--
--   **Probe interpolation.** Let $T,I,Y\subseteq E_0$ with $I\subseteq Y$, suppose that $I$ and $Y$ both lie in the class of $T$, and that $\underline\phi^{\,T}(I)\le-1$ and $\underline\phi^{\,T}(Y)>0$. Then there is $B\subseteq E_0$ with
--   $$I\subseteq B\subseteq Y,\qquad B\triangle T\ \text{small},\qquad -1<\underline\phi^{\,T}(B)\le0,$$
--   that is, $B\in\mathcal L_0(T)$ and $I\subseteq B\subseteq Y$.
--
--   The lower local rule $\mathcal L_0(T)$, together with the complementary upper rule $\{X:\ E_0\setminus X\in\mathcal L_0(E_0\setminus T)\}$, supplies the local families from which the bases of the self-dual matroid on $E_0$ are assembled. Probe interpolation settles the central case of the interval alternative for these families: when the probe lower limit is at most $-1$ at $I$ and positive at $Y$, a member of $\mathcal L_0(T)$ lies between $I$ and $Y$.
--
--   **Formalization Note** The instances are `d_infinite`, `e0_infinite`, `d_countable` and `e0_countable`; `labelEquiv : E0 ≃ ℕ` is `Denumerable.eqv` for a classically chosen `Denumerable E0` structure. `natProbe T n A = fProbe T n (labelEquiv ⁻¹' A)`, and the interval endpoints are written `labelEquiv.symm ⁻¹' I`, which is the image $\lambda(I)$. The lemmas are `natProbe_cylinder` (the property `CylinderContinuous`), `natProbe_shift` (the property `IntervalFiniteShift`) and `fProbe_interpolation`. `LocalLower T` is `{X | SameClass T X ∧ LowerBasis (fProbe T) X}`, with the lower limit `probeLiminf` taken in `EReal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/LocalBases.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/LocalBases.lean by skeleton subtraction
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

namespace OAI

section

open Set Filter
open scoped Topology symmDiff

namespace InfiniteMatroidCounterexample

instance d_infinite : Infinite D :=
  Infinite.of_injective (fun m : ℕ ↦ (⟨m, fun _ ↦ false⟩ : D))
    (fun _ _ h ↦ congrArg Sigma.fst h)

instance e0_infinite : Infinite E0 := inferInstance
instance d_countable : Countable D := inferInstance
instance e0_countable : Countable E0 := inferInstance

noncomputable def labelEquiv : E0 ≃ ℕ := by
  letI := Classical.choice (nonempty_denumerable E0)
  exact Denumerable.eqv E0

noncomputable def natProbe (T : Set E0) (n : ℕ) (A : Set ℕ) : ℝ :=
  fProbe T n (labelEquiv ⁻¹' A)

lemma natProbe_cylinder {T I Y : Set E0} (hI : SameClass T I) (hY : SameClass T Y) :
    CylinderContinuous (natProbe T) (labelEquiv.symm ⁻¹' I) (labelEquiv.symm ⁻¹' Y) := by
  classical
  intro j ε hε
  obtain ⟨N, _, hN⟩ := fProbe_block_continuity hI hY j hε
  refine ⟨(blockPrefix N).sup labelEquiv + 1, ?_⟩
  intro X Z hIX hXY hIZ hZY hagree n hnj
  apply hN (labelEquiv ⁻¹' X) (labelEquiv ⁻¹' Z)
  · intro x hx
    exact hIX (by simpa using hx)
  · intro x hx
    simpa using hXY hx
  · intro x hx
    exact hIZ (by simpa using hx)
  · intro x hx
    simpa using hZY hx
  · intro x hx
    apply hagree (labelEquiv x)
    have hle := Finset.le_sup (f := labelEquiv) ((mem_prefix x N).mpr hx)
    omega
  · exact hnj.le

lemma natProbe_shift (T : Set E0) (I Y : Set ℕ) :
    IntervalFiniteShift (natProbe T) I Y := by
  intro A B _ hAB _ hfin
  have hf : (labelEquiv ⁻¹' B \ labelEquiv ⁻¹' A).Finite := by
    rw [← Set.preimage_sdiff]
    exact Set.Finite.preimage labelEquiv.injective.injOn hfin
  have he := finite_change_eventually (T := T) (Set.preimage_mono hAB) hf
  have hc : (labelEquiv ⁻¹' B \ labelEquiv ⁻¹' A).ncard = (B \ A).ncard := by
    rw [← Set.preimage_sdiff]
    exact Set.ncard_preimage_of_injective_subset_range labelEquiv.injective
      (by rw [labelEquiv.surjective.range_eq]; exact subset_univ _)
  rw [hc] at he
  simpa only [probeLiminf, natProbe, EReal.coe_natCast] using probeLiminf_finite_change he

lemma fProbe_interpolation {T I Y : Set E0} (hI : SameClass T I) (hY : SameClass T Y)
    (hIY : I ⊆ Y) (hlow : probeLiminf (fProbe T) I ≤ -1)
    (hhigh : 0 < probeLiminf (fProbe T) Y) :
    ∃ B, I ⊆ B ∧ B ⊆ Y ∧ SameClass T B ∧ LowerBasis (fProbe T) B := by
  have hpre (X : Set E0) : labelEquiv ⁻¹' (labelEquiv.symm ⁻¹' X) = X := by
    ext x
    simp
  have hlim (X : Set E0) : probeLiminf (natProbe T) (labelEquiv.symm ⁻¹' X) =
      probeLiminf (fProbe T) X := by
    simp only [probeLiminf, natProbe, hpre]
  obtain ⟨B, hIB, hBY, hB⟩ := local_interpolation (Set.preimage_mono (f := labelEquiv.symm) hIY)
    (natProbe_cylinder hI hY)
    (fun n A B _ hAB _ ↦ fProbe_mono T (Set.preimage_mono hAB) n)
    (fun n A B _ _ _ h ↦ by
      obtain ⟨e, he⟩ := h
      calc
        natProbe T n B ≤ fProbe T n (insert (labelEquiv.symm e) (labelEquiv ⁻¹' A)) := by
          apply fProbe_mono
          intro x hx
          rcases he hx with heq | hxA
          · left
            exact labelEquiv.injective (by simpa using heq)
          · exact Or.inr hxA
        _ ≤ natProbe T n A + 1 := fProbe_insert_le _ _ _ _)
    (natProbe_shift T _ _) (by rw [hlim]; exact hlow) (by rw [hlim]; exact hhigh)
  have hi : I ⊆ labelEquiv ⁻¹' B := by
    intro x hx
    exact hIB (by simpa using hx)
  have hy : labelEquiv ⁻¹' B ⊆ Y := by
    intro x hx
    simpa using hBY hx
  exact ⟨labelEquiv ⁻¹' B, hi, hy, sameClass_interval hI hY hi hy, hB⟩

def LocalLower (T : Set E0) : Set (Set E0) :=
  {X | SameClass T X ∧ LowerBasis (fProbe T) X}

end InfiniteMatroidCounterexample
end

end OAI


