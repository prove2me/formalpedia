-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
-- name    : OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:48:27.884665+00:00
-- url     : https://prove2.me/theorems/d4297efb-fd1b-430b-95cc-8e34685bf0b1
-- title:
--   Integer sign rows satisfying the Hadamard Gram equation
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Integer sign row.** A function $h:\{0,\dots,n-1\}\to\mathbb Z$ is an integer sign row if every value $h(j)$ is $1$ or $-1$ and its row circulant $C(h)_{ij}=h(j-i)$ satisfies, over the integers,
--   $$
--   C(h)\,C(h)^{\mathsf T}=n\,I.
--   $$
--   This is the integer form of a real circulant sign Hadamard matrix; the bridge between the two uses only the injective coefficient map $\mathbb Z\to\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CirculantHadamard mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR

/-!
# From real sign matrices to integer cyclic autocorrelation

The Gram entry is reindexed using translation in `Fin n`. The real/integer
bridge uses the injective coefficient map `ℤ → ℝ`; it does not assume any
classification or any group-ring norm statement.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {n : ℕ}

/-- An integer sign row with the full Hadamard Gram equation. -/
def IsIntegerSignRow (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧
    rowCirculant h * (rowCirculant h).transpose =
      (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

end CirculantHadamard

end OAI


