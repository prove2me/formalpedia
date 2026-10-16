-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
-- name    : OAI_Combinatorics_GraphThreshold_CopyOrbits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:14:19.479987+00:00
-- url     : https://prove2.me/theorems/5cdaf14a-5ad6-42fe-aa5e-242d768137de
-- title:
--   Distinct copies of a finite set under a finite group action, their counts and uniform copy laws
-- statement:
--   Let a finite group $G$ act on a set $X$, and extend the action to finite subsets by $g\cdot F=\{g\cdot x:\ x\in F\}$. Here a copy of a finite set $F\subseteq X$ is a set of the form $g\cdot F$; copies are distinct sets, not group elements or labelled embeddings, so a set obtained from several group elements is counted once. Throughout, $F,I,U,S,J$ denote finite subsets of $X$.
--
--   1. **Copy orbit and copy count.** $\mathcal{C}(F)=\{g\cdot F:\ g\in G\}$ is the set of distinct copies of $F$, and $N(F)=|\mathcal{C}(F)|$.
--
--   2. **Internal copies.** $N_{\mathrm{in}}(I,F)=|\{J\in\mathcal{C}(F):\ J\subseteq I\}|$, the number of copies of $F$ lying inside $I$.
--
--   3. **Containing copies.** $N_{\supseteq}(I,U)=|\{J\in\mathcal{C}(I):\ U\subseteq J\}|$, the number of copies of $I$ containing $U$.
--
--   4. **Basic facts.** $J\in\mathcal{C}(F)$ if and only if $g\cdot F=J$ for some $g\in G$; $F\in\mathcal{C}(F)$, so $N(F)\ge 1$; $g\cdot J\in\mathcal{C}(F)$ if and only if $J\in\mathcal{C}(F)$, so each $g$ permutes $\mathcal{C}(F)$; $\mathcal{C}(g\cdot F)=\mathcal{C}(F)$; for the empty set, $\mathcal{C}(\emptyset)=\{\emptyset\}$, $N(\emptyset)=1$ and $N_{\mathrm{in}}(I,\emptyset)=1$; and $N_{\supseteq}(I,U)>0$ if and only if $U\subseteq g\cdot I$ for some $g\in G$.
--
--   5. **Uniform copy law and containment probability.** The copy law of $I$ is the uniform distribution on $\mathcal{C}(I)$, and the containment probability of $U$ is
--
--      $$\pi_I(U)=\Pr_{J\sim\mathrm{Unif}(\mathcal{C}(I))}\bigl[U\subseteq J\bigr]=\frac{N_{\supseteq}(I,U)}{N(I)} .$$
--
--      It satisfies $\pi_I(\emptyset)=1$, and $\pi_I(U)>0$ if and only if $U\subseteq g\cdot I$ for some $g\in G$. In particular, if $S\subseteq I$ and $S_0\in\mathcal{C}(S)$, then $\pi_I(S_0)>0$: every copy of a subset extends to a copy of the ambient set.
--
--   6. **Extension copies and the extension law.** $\mathcal{E}(I,S)=\{J\in\mathcal{C}(I):\ S\subseteq J\}$ has exactly $N_{\supseteq}(I,S)$ elements and is nonempty when $\pi_I(S)>0$. In that case the extension law of $(I,S)$ is the uniform law on $\mathcal{E}(I,S)$, which is positive (every element has positive weight). Moreover, the members of $\mathcal{E}(I,S)$ that contain $J$ are exactly the members of $\mathcal{E}(I,S\cup J)$.
--
--   In the graph application $X$ is the set of edges of $K_n$ and $G$ is the symmetric group $S_n$ acting by relabelling vertices; copies of an edge set are then unlabelled copies of a graph, and $\pi_I(U)$ is the probability that a uniformly random copy of $I$ contains the fixed edge set $U$. Extension laws are the branching laws of a tree of nested random copies, and ratios $\pi_I(S\cup J)/\pi_I(S)$ measure how spread these laws are.
--
--   **Formalization Note** The Lean names are `copyOrbit`, `OrbitCopy` (the subtype of $\mathcal{C}(F)$), `orbitCount`, `internalCopyCount`, `containingCopyCount`, `copyLaw`, `containmentProb`, `ExtensionCopy`, `extensionLaw` (which takes the proof of $\pi_I(S)>0$ as an argument) and `extensionIntersectionEquiv`; `orbitCopyEquiv g F` is the permutation of $\mathcal{C}(F)$ induced by $g$. `uniform_prob_count` and `card_filter_OrbitCopy` are decidability and counting plumbing. Only decidable equality is assumed on $X$, not finiteness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/CopyOrbits.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/CopyOrbits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability

namespace OAI

/-!
# Distinct subset copies under a finite group action

Copies are distinct orbit elements, not group elements or labeled embeddings.
All counting and probability statements therefore retain the stabilizer
multiplicities correctly, including for the empty subset.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace LeanBlast.SecondKahnKalai

universe u v

variable (G : Type u) [Group G] [Fintype G]
variable {X : Type v} [DecidableEq X] [MulAction G X]

/-- The distinct copies of a finite subset under the given action. -/
def copyOrbit (F : Finset X) : Finset (Finset X) :=
  Finset.univ.image (fun g : G => g • F)

/-- An actual distinct copy, with no labeling multiplicity. -/
abbrev OrbitCopy (F : Finset X) := {J : Finset X // J ∈ copyOrbit G F}

/-- The total number of distinct copies. -/
def orbitCount (F : Finset X) : ℕ := (copyOrbit G F).card

/-- Copies of `F` whose elements all lie in the fixed set `I`. -/
def internalCopyCount (I F : Finset X) : ℕ :=
  ((copyOrbit G F).filter (fun J => J ⊆ I)).card

/-- Copies of `I` containing the fixed observed set `U`. -/
def containingCopyCount (I U : Finset X) : ℕ :=
  ((copyOrbit G I).filter (fun J => U ⊆ J)).card

@[simp] theorem mem_copyOrbit_iff {F J : Finset X} :
    J ∈ copyOrbit G F ↔ ∃ g : G, g • F = J := by
  simp only [copyOrbit, Finset.mem_image, Finset.mem_univ, true_and]

theorem self_mem_copyOrbit (F : Finset X) : F ∈ copyOrbit G F := by
  exact (mem_copyOrbit_iff G).mpr ⟨1, one_smul _ _⟩

theorem copyOrbit_nonempty (F : Finset X) : (copyOrbit G F).Nonempty :=
  ⟨F, self_mem_copyOrbit G F⟩

theorem orbitCount_pos (F : Finset X) : 0 < orbitCount G F :=
  Finset.card_pos.mpr (copyOrbit_nonempty G F)

instance orbitCopy_nonempty (F : Finset X) : Nonempty (OrbitCopy G F) :=
  ⟨⟨F, self_mem_copyOrbit G F⟩⟩

@[simp] theorem card_OrbitCopy (F : Finset X) :
    Fintype.card (OrbitCopy G F) = orbitCount G F := Fintype.card_coe _

theorem smul_mem_copyOrbit (g : G) {F J : Finset X} (hJ : J ∈ copyOrbit G F) :
    g • J ∈ copyOrbit G F := by
  obtain ⟨h, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
  exact (mem_copyOrbit_iff G).mpr ⟨g * h, mul_smul _ _ _⟩

@[simp] theorem smul_mem_copyOrbit_iff (g : G) {F J : Finset X} :
    g • J ∈ copyOrbit G F ↔ J ∈ copyOrbit G F := by
  refine ⟨fun h => ?_, smul_mem_copyOrbit G g⟩
  simpa only [inv_smul_smul] using smul_mem_copyOrbit G g⁻¹ h

@[simp] theorem copyOrbit_smul (g : G) (F : Finset X) :
    copyOrbit G (g • F) = copyOrbit G F := by
  ext J
  constructor
  · intro hJ
    obtain ⟨h, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
    exact (mem_copyOrbit_iff G).mpr ⟨h * g, mul_smul _ _ _⟩
  · intro hJ
    obtain ⟨h, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
    apply (mem_copyOrbit_iff G).mpr
    refine ⟨h * g⁻¹, ?_⟩
    simp only [mul_smul, inv_smul_smul]

/-- The group acts bijectively on the set of actual orbit copies. -/
def orbitCopyEquiv (g : G) (F : Finset X) : OrbitCopy G F ≃ OrbitCopy G F where
  toFun J := ⟨g • J.val, smul_mem_copyOrbit G g J.property⟩
  invFun J := ⟨g⁻¹ • J.val, smul_mem_copyOrbit G g⁻¹ J.property⟩
  left_inv _ := Subtype.ext (inv_smul_smul _ _)
  right_inv _ := Subtype.ext (smul_inv_smul _ _)

@[simp] theorem orbitCopyEquiv_val (g : G) (F : Finset X) (J : OrbitCopy G F) :
    (orbitCopyEquiv G g F J).val = g • J.val := rfl

@[simp] theorem copyOrbit_empty : copyOrbit G (∅ : Finset X) = {∅} := by
  ext J
  simp only [mem_copyOrbit_iff, Finset.smul_finset_empty, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact h.symm
  · intro h
    exact ⟨1, h.symm⟩

@[simp] theorem orbitCount_empty : orbitCount G (∅ : Finset X) = 1 := by
  simp [orbitCount]

@[simp] theorem internalCopyCount_empty (I : Finset X) :
    internalCopyCount G I ∅ = 1 := by
  simp [internalCopyCount, Finset.filter_singleton, Finset.empty_subset]

theorem containingCopyCount_pos_iff (I U : Finset X) :
    0 < containingCopyCount G I U ↔ ∃ g : G, U ⊆ g • I := by
  rw [containingCopyCount, Finset.card_pos]
  constructor
  · rintro ⟨J, hJ⟩
    obtain ⟨hcopy, hsub⟩ := Finset.mem_filter.mp hJ
    obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hcopy
    exact ⟨g, hsub⟩
  · rintro ⟨g, hg⟩
    refine ⟨g • I, Finset.mem_filter.mpr ⟨?_, hg⟩⟩
    exact (mem_copyOrbit_iff G).mpr ⟨g, rfl⟩

/-- The uniform law on distinct copies, rather than on labeled embeddings. -/
def copyLaw (I : Finset X) : FiniteLaw (OrbitCopy G I) :=
  FiniteLaw.uniform (OrbitCopy G I)

/-- Probability that a uniform actual copy contains an observed finite set. -/
def containmentProb (I U : Finset X) : ℝ :=
  (copyLaw G I).prob (fun J => U ⊆ J.val)

/-- Expose the generic uniform formula with the caller's decidable predicate.
The finite sets are equal extensionally even when the generic probability
definition uses its own classical decision procedure. -/
 theorem uniform_prob_count (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] :
    (FiniteLaw.uniform Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  have hfilter : @Finset.filter Ω P (fun ω => Classical.propDecidable (P ω)) Finset.univ =
      Finset.univ.filter P := by
    ext ω
    simp only [Finset.mem_filter]
  rw [FiniteLaw.uniform_prob, hfilter]

theorem card_filter_OrbitCopy (I : Finset X) (P : Finset X → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (OrbitCopy G I)).filter (fun J => P J.val)).card =
      ((copyOrbit G I).filter P).card := by
  have h : (∑ J : OrbitCopy G I, if P J.val then (1 : ℕ) else 0) =
      ∑ J ∈ copyOrbit G I, if P J then 1 else 0 :=
    Finset.sum_coe_sort (copyOrbit G I) (fun J => if P J then (1 : ℕ) else 0)
  simpa only [Finset.sum_boole, Nat.cast_id] using h

theorem containmentProb_eq_count (I U : Finset X) :
    containmentProb G I U = (containingCopyCount G I U : ℝ) / orbitCount G I := by
  rw [containmentProb, copyLaw, uniform_prob_count, card_OrbitCopy]
  exact congrArg (fun k : ℕ => (k : ℝ) / (orbitCount G I : ℝ))
    (card_filter_OrbitCopy G I (fun J => U ⊆ J))

@[simp] theorem containmentProb_empty (I : Finset X) : containmentProb G I ∅ = 1 := by
  simp [containmentProb]

theorem containmentProb_pos_iff (I U : Finset X) :
    0 < containmentProb G I U ↔ ∃ g : G, U ⊆ g • I := by
  rw [containmentProb_eq_count,
    div_pos_iff_of_pos_right (Nat.cast_pos.mpr (orbitCount_pos G I)), Nat.cast_pos]
  exact containingCopyCount_pos_iff G I U

/-- Every copy of a subset extends to at least one copy of its ambient set. -/
theorem containmentProb_pos_of_copy_subset {S I S₀ : Finset X}
    (hSI : S ⊆ I) (hS₀ : S₀ ∈ copyOrbit G S) : 0 < containmentProb G I S₀ := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hS₀
  exact (containmentProb_pos_iff G I (g • S)).mpr
    ⟨g, Finset.smul_finset_subset_smul_finset_iff.mpr hSI⟩

/-- Actual distinct extensions of the observed predecessor. Histories in a
tree may index this same family separately; this type never merges histories. -/
abbrev ExtensionCopy (I S : Finset X) := {J : OrbitCopy G I // S ⊆ J.val}

theorem extensionCopy_nonempty {I S : Finset X}
    (hpos : 0 < containmentProb G I S) : Nonempty (ExtensionCopy G I S) := by
  obtain ⟨g, hg⟩ := (containmentProb_pos_iff G I S).mp hpos
  exact ⟨⟨⟨g • I, (mem_copyOrbit_iff G).mpr ⟨g, rfl⟩⟩, hg⟩⟩

@[simp] theorem card_ExtensionCopy (I S : Finset X) :
    Fintype.card (ExtensionCopy G I S) = containingCopyCount G I S := by
  rw [Fintype.card_subtype, card_filter_OrbitCopy]
  rfl

/-- The uniform law on actual copies extending `S`, with positivity justified
by the actual containment event. -/
def extensionLaw (I S : Finset X) (hpos : 0 < containmentProb G I S) :
    FiniteLaw (ExtensionCopy G I S) := by
  let : Nonempty (ExtensionCopy G I S) := extensionCopy_nonempty G hpos
  exact FiniteLaw.uniform (ExtensionCopy G I S)

theorem extensionLaw_isPositive (I S : Finset X) (hpos : 0 < containmentProb G I S) :
    (extensionLaw G I S hpos).IsPositive := by
  let : Nonempty (ExtensionCopy G I S) := extensionCopy_nonempty G hpos
  exact FiniteLaw.uniform_isPositive _

def extensionIntersectionEquiv (I S J : Finset X) :
    {C : ExtensionCopy G I S // J ⊆ C.val.val} ≃ ExtensionCopy G I (S ∪ J) where
  toFun C := ⟨C.val.val, Finset.union_subset_iff.mpr ⟨C.val.property, C.property⟩⟩
  invFun C := ⟨⟨C.val, (Finset.union_subset_iff.mp C.property).1⟩,
    (Finset.union_subset_iff.mp C.property).2⟩
  left_inv C := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv C := by apply Subtype.ext; rfl

end LeanBlast.SecondKahnKalai

end

end OAI


