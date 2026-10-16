-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
-- name    : OAI_Combinatorics_TreeEdit_SampledSpectrum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:29:38.919515+00:00
-- url     : https://prove2.me/theorems/47478f72-e337-4529-bf4e-c03a14909af4
-- title:
--   High-frequency mass and the spectral bound for sampled circle-tree words
-- statement:
--   Let $M\ge1$, let $\mathcal{S}_h=\mathcal{S}_h(\mathbb{Z}/M\mathbb{Z})$ be the group of residue vectors indexed by the leaves of the complete $m$-ary tree of height $h$, and for a character $\chi$ of $\mathcal{S}_h$ let $\operatorname{cen}(\operatorname{sum}\chi)\in\mathbb{Z}$ be the centered frequency of its summary $\chi\circ\Delta_h$, where $\Delta_h$ puts the same residue at every leaf; the frequency $\xi$ of a character $a\mapsto e^{2\pi i\xi a/M}$ of $\mathbb{Z}/M\mathbb{Z}$ is centered by choosing its integer representative $c$ with $-M<2c\le M$. Weights are functions $H$ from the characters of $\mathcal{S}_h$ to $\mathbb{R}$.
--
--   1. **High indicator.** For $Q\in\mathbb{N}$, $\operatorname{high}_Q(\chi)=1$ if $Q\le|\operatorname{cen}(\operatorname{sum}\chi)|$, and $0$ otherwise.
--
--   2. **High mass.** $\operatorname{HM}_Q(H)=\sum_{\chi}\operatorname{high}_Q(\chi)\,H(\chi)$.
--
--   3. **Spectral bound.** Fix circle-tree data: a labelling $r$ of a pool, a list $j$ of $g$ pool indices, $T$ rows, $R\ge1$ bins and a configuration $C$ of height $h$ with $m=gs$ children per node, and let $Y_C(x)$ be the circle-tree word of $C$ at the sampled leaf phases $x/M \bmod 1$. Weights $H$ satisfy the spectral bound with constant $D\in\mathbb{R}$ if for every $z\in\mathcal{S}_h$
--
--      $$\sum_{\chi}|1-\chi(z)|^2\,H(\chi)\ \le\ D\cdot\mathbb{E}_{x\in\mathcal{S}_h}\operatorname{ed}\bigl(Y_C(x),Y_C(x+z)\bigr),$$
--
--      where $\operatorname{ed}$ is unit-cost edit distance and $\mathbb{E}$ is the uniform average over $\mathcal{S}_h$.
--
--   If $F:\mathcal{S}_h\to\ell_1$ satisfies $\|F(x)-F(y)\|_1\le D\operatorname{ed}(Y_C(x),Y_C(y))$, then the spectral weights of its averaged displacement satisfy the spectral bound with constant $D$. Under divisibility hypotheses on the periods, the bound passes from a node to each child, with $D$ multiplied by $T$, after pushing the weights forward along the child embedding; combined with estimates on the high mass it bounds the averaged displacement under the root half-turn.
--
--   **Formalization Note** The Lean names are `TorusFourier.high`, `highMass` and `SpectralBound r j T h C H D`; the left side is `energy H z`, the right side uses `mean` over the finite group `State (ZMod M) (g*s) h` and `sampledWord`, and `NeZero M`, `NeZero R` are assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/SampledSpectrum.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/SampledSpectrum.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

noncomputable def high {M m : ℕ} [NeZero M] (h Q : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) : ℝ :=
  if (Q : ℝ) ≤ |(centered (summary h χ) : ℝ)| then 1 else 0

noncomputable def highMass {M m : ℕ} [NeZero M] (h Q : ℕ) (H : AddChar (State (ZMod M) m h) ℂ → ℝ) : ℝ :=
  ∑ χ, high h Q χ * H χ

def SpectralBound {I : Type} {g s L M R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (T h : ℕ) (C : Config I L (g*s) h)
    (H : AddChar (State (ZMod M) (g*s) h) ℂ → ℝ) (D : ℝ) : Prop := ∀ z,
      energy H z ≤ D * mean (fun x : State (ZMod M) (g*s) h =>
        (ed (sampledWord r j T R h C x).val (sampledWord r j T R h C (x+z)).val : ℝ))

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

end TreeEdit.TorusFourier

end OAI


