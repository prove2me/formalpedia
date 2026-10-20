-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
-- name    : OAI_Combinatorics_BinaryEdit_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:33:16.405072+00:00
-- url     : https://prove2.me/theorems/490515c6-fd72-4e4a-9835-ca7ea600985e
-- title:
--   Length-indexed deficits and capped word sets
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words.
--
--   1. **Deficit at length $n$.**
--   $$
--   r_n(x,y)=n-\mathrm{lcs}(x,y),
--   $$
--   used on pairs of words of length $n$; it is zero exactly when $x=y$.
--   2. **Capped words.** $W_{\le d}(\alpha)$, the words over $\alpha$ of length at most $d$, including the empty word.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BinaryEditLower mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower

namespace OAI
noncomputable section

namespace TreeEdit.BinaryLower

universe u v

/-- The one-sided deficit `r_n`, used on pairs of length `n`. -/
def deficit {α : Type u} (n : ℕ) (x y : List α) : ℕ := n - lcs x y

/-- Words of length at most the specified cap. -/
abbrev WordsLE (α : Type u) (d : ℕ) := {x : List α // x.length ≤ d}

end TreeEdit.BinaryLower

end

end OAI


