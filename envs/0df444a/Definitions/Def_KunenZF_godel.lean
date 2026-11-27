-- Prove2me | Definitions.Def_KunenZF_godel
-- name    : KunenZF_godel
-- status  : Definition
-- author  : @teargosling
-- created : 2026-11-27T05:02:11.548651+00:00
-- url     : https://prove2.me/theorems/81b88528-726c-56cf-bfc0-7edb85b5624e
-- title:
--   Gödel set operations and cofinal Gödel-preserving embeddings on $\{\in, j\}$-structures
-- statement:
--   Defines the 12 Gödel set operations semantically on any $\{\in, j\}$-structure $M$ (`setLangJ.Structure M`), together with the predicate `IsGodelCofinalEmb k` for a map $k : M \to M$.
--
--   Writing $a \in^M b$ for `MemRelM a b` and $\langle a, b \rangle$ for the Kuratowski ordered pair $\{\{a\}, \{a, b\}\}$ (`IsPairM`), the 12 operations capture:
--
--   1. Unordered pair $\{a, b\}$ (`IsDblM`), big union $\bigcup x$ (`IsUnionM`), set difference $x \setminus y$ (`IsDiffM`), Cartesian product $x \times y$ (`IsProdM`), and domain $\operatorname{dom}(x)$ (`IsDomM`).
--   2. Membership graph $\{\langle a, b \rangle \in x \times x \mid a \in b\}$ (`IsMemGraphM`) and diagonal graph $\{\langle a, a \rangle \mid a \in x\}$ (`IsEqGraphM`).
--   3. Tuple permutations and reassociations: converse `IsSwapM` ($\langle a, b \rangle \mapsto \langle b, a \rangle$), `IsPullM` ($\langle a, \langle b, c \rangle \rangle \mapsto \langle \langle a, b \rangle, c \rangle$), `IsPushM` ($\langle \langle a, b \rangle, c \rangle \mapsto \langle a, \langle b, c \rangle \rangle$), `IsShiftM` ($\langle a, \langle b, c \rangle \rangle \mapsto \langle b, \langle a, c \rangle \rangle$), and `IsInnerShiftM` ($\langle d, \langle a, \langle b, c \rangle \rangle \rangle \mapsto \langle d, \langle b, \langle a, c \rangle \rangle \rangle$).
--
--   A map $k : M \to M$ satisfies `IsGodelCofinalEmb k` when $k$ preserves $\in^M$, is cofinal in $M$ ($\forall y \in M\, \exists x \in M,\; y \in^M k(x)$), and preserves all 12 Gödel operations. Together these finite first-order conditions are sufficient for $\Delta_0$-elementarity via Gödel's finite basis and full elementarity in $\mathrm{ZF}(j)$ via Gaifman's Lemma (1974).
-- source:
--   Kurt Gödel, The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory, Annals of Mathematics Studies 3 (1940), Chapter II; Haim Gaifman, Elementary embeddings of models of set-theory and certain subtheories, Proc. Sympos. Pure Math. XIII, Part II (1974), pp. 33-101, Theorem 1; Akira Suzuki, No elementary embedding from V into V is definable from parameters, J. Symbolic Logic 64 (1999), 1591-1594, https://doi.org/10.2307/2586799.

import Mathlib.ModelTheory.Semantics
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

/-!
# Gödel set operations and cofinal Gödel-preserving embeddings on `setLangJ`-structures

Defines the 12 Gödel set operations (`{a, b}`, `⋃`, `\`, `×`, `dom`, membership graph,
equality graph, and tuple shuffles) semantically on any `setLangJ.Structure M`, together with
the predicate `IsGodelCofinalEmb k` stating that a map `k : M → M` preserves `∈`, is cofinal,
and preserves all 12 Gödel operations.
-/

universe u

namespace KunenZF

open FirstOrder FirstOrder.Language

section GodelOps

variable {M : Type u} [setLangJ.Structure M]

/-- Membership relation in a `setLangJ`-structure `M`. -/
def MemRelM (a b : M) : Prop :=
  Structure.RelMap (L := setLangJ) ContinuumHypothesis.SetRel.mem ![a, b]

/-- `s` is the singleton `{a}` in `M`. -/
def IsSingM (s a : M) : Prop :=
  ∀ z : M, MemRelM z s ↔ z = a

/-- `d` is the unordered pair `{a, b}` in `M`. -/
def IsDblM (d a b : M) : Prop :=
  ∀ z : M, MemRelM z d ↔ z = a ∨ z = b

/-- `p` is the Kuratowski ordered pair `⟨a, b⟩ = {{a}, {a, b}}` in `M`. -/
def IsPairM (p a b : M) : Prop :=
  ∀ w : M, MemRelM w p ↔ IsSingM w a ∨ IsDblM w a b

/-- `u` is the big union `⋃ x` in `M`. -/
def IsUnionM (u x : M) : Prop :=
  ∀ z : M, MemRelM z u ↔ ∃ y : M, MemRelM y x ∧ MemRelM z y

/-- `d` is the set difference `x \ y` in `M`. -/
def IsDiffM (d x y : M) : Prop :=
  ∀ z : M, MemRelM z d ↔ MemRelM z x ∧ ¬ MemRelM z y

/-- `r` is the Cartesian product `x × y` in `M`. -/
def IsProdM (r x y : M) : Prop :=
  ∀ p : M, MemRelM p r ↔ ∃ a b : M, MemRelM a x ∧ MemRelM b y ∧ IsPairM p a b

/-- `d` is the domain `{a | ∃ b, ⟨a, b⟩ ∈ x}` in `M`. -/
def IsDomM (d x : M) : Prop :=
  ∀ a : M, MemRelM a d ↔ ∃ b p : M, IsPairM p a b ∧ MemRelM p x

/-- `r` is the membership graph `{⟨a, b⟩ ∈ x × x | a ∈ b}` in `M`. -/
def IsMemGraphM (r x : M) : Prop :=
  ∀ p : M, MemRelM p r ↔
    ∃ a b : M, MemRelM a x ∧ MemRelM b x ∧ MemRelM a b ∧ IsPairM p a b

/-- `r` is the equality graph `{⟨a, a⟩ | a ∈ x}` in `M`. -/
def IsEqGraphM (r x : M) : Prop :=
  ∀ p : M, MemRelM p r ↔ ∃ a : M, MemRelM a x ∧ IsPairM p a a

/-- `r` is the converse `{⟨b, a⟩ | ⟨a, b⟩ ∈ x}` in `M`. -/
def IsSwapM (r x : M) : Prop :=
  ∀ p : M, MemRelM p r ↔ ∃ a b q : M, IsPairM p b a ∧ IsPairM q a b ∧ MemRelM q x

/-- `r` is `{⟨⟨a, b⟩, c⟩ | ⟨a, ⟨b, c⟩⟩ ∈ x}` in `M`. -/
def IsPullM (r x : M) : Prop :=
  ∀ p : M, MemRelM p r ↔
    ∃ a b c ab bc q : M,
      IsPairM ab a b ∧ IsPairM p ab c ∧ IsPairM bc b c ∧ IsPairM q a bc ∧ MemRelM q x

/-- `r` is `{⟨a, ⟨b, c⟩⟩ | ⟨⟨a, b⟩, c⟩ ∈ x}` in `M`. -/
def IsPushM (r x : M) : Prop :=
  ∀ p : M, MemRelM p r ↔
    ∃ a b c ab bc q : M,
      IsPairM bc b c ∧ IsPairM p a bc ∧ IsPairM ab a b ∧ IsPairM q ab c ∧ MemRelM q x

/-- `r` is `{⟨b, ⟨a, c⟩⟩ | ⟨a, ⟨b, c⟩⟩ ∈ x}` in `M`. -/
def IsShiftM (r x : M) : Prop :=
  ∀ p : M, MemRelM p r ↔
    ∃ a b c ac bc q : M,
      IsPairM ac a c ∧ IsPairM p b ac ∧ IsPairM bc b c ∧ IsPairM q a bc ∧ MemRelM q x

/-- `r` is `{⟨d, ⟨b, ⟨a, c⟩⟩⟩ | ⟨d, ⟨a, ⟨b, c⟩⟩⟩ ∈ x}` in `M`. -/
def IsInnerShiftM (r x : M) : Prop :=
  ∀ p : M, MemRelM p r ↔
    ∃ d a b c ac bac bc abc q : M,
      IsPairM ac a c ∧ IsPairM bac b ac ∧ IsPairM p d bac ∧
      IsPairM bc b c ∧ IsPairM abc a bc ∧ IsPairM q d abc ∧ MemRelM q x

/-- A map `k : M → M` is a cofinal Gödel-preserving embedding if it preserves `∈`, is cofinal,
and preserves the 12 Gödel set operations. -/
structure IsGodelCofinalEmb (k : M → M) : Prop where
  pres_mem : ∀ x y : M, MemRelM x y ↔ MemRelM (k x) (k y)
  cofinal : ∀ y : M, ∃ x : M, MemRelM y (k x)
  pres_dbl : ∀ d a b : M, IsDblM d a b → IsDblM (k d) (k a) (k b)
  pres_union : ∀ u x : M, IsUnionM u x → IsUnionM (k u) (k x)
  pres_diff : ∀ d x y : M, IsDiffM d x y → IsDiffM (k d) (k x) (k y)
  pres_prod : ∀ r x y : M, IsProdM r x y → IsProdM (k r) (k x) (k y)
  pres_dom : ∀ d x : M, IsDomM d x → IsDomM (k d) (k x)
  pres_memGraph : ∀ r x : M, IsMemGraphM r x → IsMemGraphM (k r) (k x)
  pres_eqGraph : ∀ r x : M, IsEqGraphM r x → IsEqGraphM (k r) (k x)
  pres_swap : ∀ r x : M, IsSwapM r x → IsSwapM (k r) (k x)
  pres_pull : ∀ r x : M, IsPullM r x → IsPullM (k r) (k x)
  pres_push : ∀ r x : M, IsPushM r x → IsPushM (k r) (k x)
  pres_shift : ∀ r x : M, IsShiftM r x → IsShiftM (k r) (k x)
  pres_innerShift : ∀ r x : M, IsInnerShiftM r x → IsInnerShiftM (k r) (k x)

end GodelOps

end KunenZF


