-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
-- name    : OAI_Combinatorics_TreeEdit_CircleFourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:27:41.051846+00:00
-- url     : https://prove2.me/theorems/d7e6181b-0fbc-4045-b2ef-5a250a7bd32b
-- title:
--   Frequencies of characters of $\mathbb{Z}/M\mathbb{Z}$ and diagonal summaries of tree characters
-- statement:
--   Let $M\ge1$ be an integer. Every additive character of $\mathbb{Z}/M\mathbb{Z}$ has the form $a\mapsto e^{2\pi i\,\xi a/M}$ for a unique $\xi\in\mathbb{Z}/M\mathbb{Z}$, with $\xi a$ read modulo $M$. Let $\mathcal{S}_h=\mathcal{S}_h(\mathbb{Z}/M\mathbb{Z})\cong(\mathbb{Z}/M\mathbb{Z})^{m^h}$ be the group of residue vectors indexed by the leaves of the complete $m$-ary tree of height $h$, and $\Delta_h:\mathbb{Z}/M\mathbb{Z}\to\mathcal{S}_h$ the diagonal map placing the same residue at every leaf.
--
--   1. **Frequency.** For a character $\chi$ of $\mathbb{Z}/M\mathbb{Z}$, $\operatorname{freq}(\chi)$ is the unique $\xi\in\mathbb{Z}/M\mathbb{Z}$ with
--
--      $$\chi(a)=\exp\Bigl(\frac{2\pi i\,\xi a}{M}\Bigr)\qquad(a\in\mathbb{Z}/M\mathbb{Z}).$$
--
--   2. **Centered frequency.** $\operatorname{cen}(\chi)\in\mathbb{Z}$ is the representative of $\operatorname{freq}(\chi)$ of least absolute value, normalised by $-M<2\operatorname{cen}(\chi)\le M$.
--
--   3. **Summary.** For a character $\chi$ of $\mathcal{S}_h$, its summary is the character $\chi\circ\Delta_h$ of $\mathbb{Z}/M\mathbb{Z}$. If $\chi(x)=\prod_u e^{2\pi i\,\xi_u x_u/M}$ over the leaves $u$, the summary has frequency $\sum_u\xi_u$.
--
--   The summary of a character records how it reacts to moving all phases below a node by the same amount. In the Fourier detection argument for the circle-phase tree a frequency is tested in three ways: a large centered summary at some node is detected by tiny common rotations of the leaves below it, a nonzero congruence of the coefficient-weighted child summaries modulo a period is detected by row shifts, and the remaining frequencies are forced to branch through many children down to many leaves.
--
--   **Formalization Note** The Lean names are `TorusFourier.frequency` (namely `AddChar.zmodAddEquiv.symm χ`), `centered` (the `ZMod.valMinAbs` of the frequency) and `summary h χ` (namely `χ.compAddMonoidHom (diagonal h)`); `NeZero M` is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleFourier.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleFourier.lean by skeleton subtraction
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

namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical

noncomputable def frequency {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) : ZMod M :=
  AddChar.zmodAddEquiv.symm χ

noncomputable def centered {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) : ℤ :=
  (frequency χ).valMinAbs

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical
open TorusTree

noncomputable def summary {M m : ℕ} [NeZero M] (h : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) : AddChar (ZMod M) ℂ :=
  χ.compAddMonoidHom (diagonal (A := ZMod M) (m := m) h)

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree

end TreeEdit.TorusFourier

end OAI


