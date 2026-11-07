-- Prove2me | Definitions.Def_MMSDelta2_Delta2P
-- name    : MMSDelta2_Delta2P
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:32.77387+00:00
-- url     : https://prove2.me/theorems/e8793042-437a-4324-9103-c10f76b7f515
-- title:
--   The class $\Delta_2^P=\mathrm P^{\mathrm{NP}}$, $\Delta_2^P$-hardness and $\Delta_2^P$-completeness
-- statement:
--   The class $\Delta_2^P$, also written $\mathrm P^{\mathrm{NP}}$, consists of the languages $L\subseteq\{0,1\}^*$ for which there are a language $A\in\mathrm{NP}$ and a deterministic polynomial-time oracle Turing machine that decides $L$ when its oracle answers membership in $A$:
--
--   $$\Delta_2^P=\bigcup_{A\in\mathrm{NP}}\mathrm P^{A}.$$
--
--   A polynomial-time machine makes polynomially many (adaptive) oracle queries, so this is the class of problems decidable in polynomial time with polynomially many adaptive queries to an NP oracle.
--
--   1. A language $L$ is **$\Delta_2^P$-hard** if every $L'\in\Delta_2^P$ reduces to it by a polynomial-time many-one reduction: $L'\le_p L$.
--   2. $L$ is **$\Delta_2^P$-complete** if $L\in\Delta_2^P$ and $L$ is $\Delta_2^P$-hard.
--   3. A promise problem $\Pi=(\Pi_{\mathrm{YES}},\Pi_{\mathrm{NO}})$ (two disjoint sets of strings) is **$\Delta_2^P$-hard** if for every $L'\in\Delta_2^P$ there is a polynomial-time computable $f$ with $x\in L'\Rightarrow f(x)\in\Pi_{\mathrm{YES}}$ and $x\notin L'\Rightarrow f(x)\in\Pi_{\mathrm{NO}}$.
--   4. For a promise set $\mathrm{Dom}$ and a set $\mathrm{Yes}$, the promise problem "decide $\mathrm{Yes}$ on $\mathrm{Dom}$" has $\Pi_{\mathrm{YES}}=\mathrm{Dom}\cap\mathrm{Yes}$ and $\Pi_{\mathrm{NO}}=\mathrm{Dom}\setminus\mathrm{Yes}$.
--
--   These are the complexity notions of every hardness and completeness statement of the mission.
--
--   **Formalization Note** Machines are the published one-tape Cook machines (`CookPvsNP.NP`, `CookPvsNP.PolyTimeComputable`, `CookPvsNP.PolyReducible`) and the published two-tape oracle machine of `KarpLiptonOM`; `KarpLiptonOM.InP (toPromise A) L` says that a polynomial-time oracle machine decides $L$ with oracle $A$. All languages are over $\{0,1\}$.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §4 'Complexity classes and source problems', p.12 (PDF p.14)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_InP
import Definitions.Def_KarpLiptonOM_toPromise
import Definitions.Def_KarpLiptonOM_PromiseProblem

namespace MMSDelta2

/-!
# The class `Δ₂ᴾ = P^NP`, `Δ₂ᴾ`-hardness and `Δ₂ᴾ`-completeness

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §4 "Complexity classes and source problems",
p.12 (PDF p.14): "We establish our hardness results using standard polynomial-time many-one
reductions." and "The class Δ₂ᴾ (also denoted by P^NP) is the class of problems decidable in
polynomial time with polynomially many adaptive queries to an NP oracle."

**Formalization Note.**
* Machines are the published one-tape Cook machines (`CookPvsNP.P`, `CookPvsNP.NP`,
  `CookPvsNP.PolyTimeComputable`, `CookPvsNP.PolyReducible`) and the published two-tape oracle
  machine `KarpLiptonOM.OracleTM`; `KarpLiptonOM.InP (toPromise A) L` says that a polynomial-time
  oracle machine decides `L` with oracle `A`. `Δ₂ᴾ` is `⋃_{A ∈ NP} P^A`. A polynomial-time machine
  makes polynomially many (adaptive) queries, so this is the paper's class.
* All languages are over the alphabet `Bool`.
* A promise problem `Π` is `Δ₂ᴾ`-hard when every `Δ₂ᴾ` language `L` has a polynomial-time `f`
  mapping members of `L` into `Π_YES` and non-members into `Π_NO`.
-/

/-- `Δ₂ᴾ = P^NP` (p.12): the languages over `{0,1}` decided by a polynomial-time oracle machine with
an oracle language in `NP`. -/
def Delta2P : Set (Set (List Bool)) :=
  {L | ∃ A ∈ CookPvsNP.NP Bool, KarpLiptonOM.InP (KarpLiptonOM.toPromise A) L}

/-- `L` is `Δ₂ᴾ`-hard under polynomial-time many-one reductions (p.12). -/
def Delta2PHard (L : Set (List Bool)) : Prop :=
  ∀ L' ∈ Delta2P, CookPvsNP.PolyReducible L' L

/-- `L` is `Δ₂ᴾ`-complete: `L ∈ Δ₂ᴾ` and `L` is `Δ₂ᴾ`-hard. -/
def Delta2PComplete (L : Set (List Bool)) : Prop :=
  L ∈ Delta2P ∧ Delta2PHard L

/-- A promise problem `Π` is `Δ₂ᴾ`-hard: every `Δ₂ᴾ` language reduces to it by a polynomial-time
many-one map sending members to `Π_YES` and non-members to `Π_NO`. -/
def Delta2PHardPromise (PP : KarpLiptonOM.PromiseProblem) : Prop :=
  ∀ L' ∈ Delta2P, ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
    ∀ x, (x ∈ L' → f x ∈ PP.yes) ∧ (x ∉ L' → f x ∈ PP.no)

/-- The promise problem with promise set `Dom` asking for membership in `Yes`:
`Π_YES = Dom ∩ Yes`, `Π_NO = Dom \ Yes`. -/
def promiseOn (Dom Yes : Set (List Bool)) : KarpLiptonOM.PromiseProblem :=
  ⟨Dom ∩ Yes, Dom \ Yes, Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1.2⟩

end MMSDelta2


