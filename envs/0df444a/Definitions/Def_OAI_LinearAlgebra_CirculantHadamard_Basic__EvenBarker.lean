-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:36:39.387999+00:00
-- url     : https://prove2.me/theorems/37408102-1b68-4541-86ec-35831a0ac761
-- title:
--   The circulant matrix of a first row
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Row circulant.** For a function $h:\{0,\dots,n-1\}\to R$, with indices added and subtracted modulo $n$, the row circulant is the $n\times n$ matrix
--   $$
--   C(h)_{ij}=h(j-i).
--   $$
--   2. **First row.** For $n>0$, row $0$ of $C(h)$ is $h$ itself, so a circulant matrix is determined by its first row.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour

namespace OAI

universe uR

namespace CirculantHadamard

def rowCirculant {n : ℕ} {R : Type uR} (h : Fin n → R) :
    Matrix (Fin n) (Fin n) R := fun i j => h (j - i)

@[simp] theorem rowCirculant_apply {n : ℕ} {R : Type uR}
    (h : Fin n → R) (i j : Fin n) : rowCirculant h i j = h (j - i) := rfl

@[simp] theorem rowCirculant_zero_row {n : ℕ} [NeZero n]
    {R : Type uR} (h : Fin n → R) (j : Fin n) : rowCirculant h 0 j = h j := by
  simp [rowCirculant]

end CirculantHadamard

end OAI


