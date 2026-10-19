-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
-- name    : OAI_RepresentationTheory_Saxl_PathContraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:01:44.549482+00:00
-- url     : https://prove2.me/theorems/b2c7751f-794d-4b70-bbd0-a47c12e80814
-- title:
--   Path band word and twisted matrix-chain contraction over a four-letter alphabet
-- statement:
--   Letters are elements of $\{0,1,2,3\}$, each identified with a pair $x=(x^{(1)},x^{(2)})\in\{0,1\}^2$ by $x=2x^{(1)}+x^{(2)}$. For $n\in\mathbb{N}$, $[n]=\{0,\dots,n-1\}$, a word is a map $w:[n]\to\{0,1,2,3\}$, and $W_{n,4}$ is the space of complex functions on words; $[P]$ denotes the Iverson bracket ($1$ if $P$ holds, $0$ otherwise). Matrices are complex $2\times2$ matrices indexed by $\{0,1\}$; $\operatorname{adj}(X)$ is the adjugate and, for $q\in\mathbb{N}$, $D_q(X)=\operatorname{adj}(X)$ if $q$ is even and $D_q(X)=X$ if $q$ is odd. The file introduces:
--
--   1. **The matrix $J$.**
--   $$
--   J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
--   $$
--   2. **Path positions.** For $r\in\mathbb{N}$ and $i\in[r]$, the positions $2i$, $2i+1$, $2i+2$ in $[2r+1]$ (left, middle and right position of the $i$-th step).
--   3. **Band word.** The vector $\beta_r\in W_{2r+1,4}$,
--   $$
--   \beta_r(w)=\big[w_0^{(1)}=0\big]\,\big[w_{2r}^{(2)}=0\big]\prod_{i=0}^{r-1}J\big(w^{(2)}_{2i},\,w^{(2)}_{2i+1}\big)\,J\big(w^{(1)}_{2i+1},\,w^{(1)}_{2i+2}\big).
--   $$
--   The first components are paired along the steps $(2i+1,2i+2)$ and the second components along the steps $(2i,2i+1)$; the endpoint conditions fix the first component at position $0$ and the second component at position $2r$ to be $0$.
--   4. **Pure matrix words.** For matrices $X_0,\dots,X_{n-1}$, the vector $\pi_X\in W_{n,4}$ with $\pi_X(w)=\prod_{i\in[n]}(X_i)_{w_i^{(1)}\,w_i^{(2)}}$, i.e. the pure tensor $X_0\otimes\cdots\otimes X_{n-1}$ under the identification of $2\times2$ matrices with $\mathbb{C}^4$.
--   5. **Matrix units.** For a letter $x$, the matrix unit $E(x)=E_{x^{(1)}x^{(2)}}$ with a single entry $1$ in row $x^{(1)}$ and column $x^{(2)}$.
--   6. **Twisted chain product.** The linear map $X\mapsto D_q(X)$, and the multilinear map in $n$ matrix arguments
--   $$
--   \operatorname{chain}_{n,p}(X_0,\dots,X_{n-1})=D_p(X_0)\,D_{p+1}(X_1)\cdots D_{p+n-1}(X_{n-1}).
--   $$
--
--   In the surrounding development $\beta_r$ encodes, in path order, the band factor of the cut staircase generator for the width-two band of the staircase $\delta_m$ (with $r=m-1$). Precisely, let $\alpha_r=e_0\otimes(e_0\otimes e_1-e_1\otimes e_0)^{\otimes r}$ be the alternating pair tensor, viewed as a function on words of length $2r+1$ over $\{0,1\}$, and for a word $w$ over $\{0,1,2,3\}$ let $w^{(1)}$ and $w^{(2)}$ be the words of first and second components of its letters. Then $\beta_r(w)=(-1)^r\,\alpha_r\big(w^{(1)}\big)\,\alpha_r\big(\overleftarrow{w^{(2)}}\big)$, where $\overleftarrow{v}$ is the word $v$ read backwards; in particular $\beta_r$ has real coefficients. Its role is the contraction identity $\sum_w\beta_r(w)\,\pi_X(w)=(-1)^r\big(\operatorname{chain}_{2r+1,1}(X_0,\dots,X_{2r})\big)_{00}$: pairing the band word with a pure tensor of matrices computes the top-left entry of a product of matrices and adjugates, which reduces the nonvanishing of homomorphisms into the band cyclic module to $2\times2$ matrix computations.
--
--   **Formalization Note** These definitions live in the namespace `Saxl.Path`: `Mat` and `Letter` abbreviate the matrix type and the four-letter alphabet, the splitting of a letter is `parts` (via `finProdFinEquiv`), and the objects are `J`, `leftPos`, `midPos`, `rightPos`, `bandWord`, `pureWord`, `entry`, `DL` (the linear map $D_q$, built on `Band.D`) and `chainML` (a `MultilinearMap`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/PathContraction.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/PathContraction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Letter := Fin 4

def parts (x : Letter) : Fin 2 × Fin 2 := finProdFinEquiv.symm x
def J : Mat := !![0, 1; -1, 0]

def leftPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val, by omega⟩
def midPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 1, by omega⟩
def rightPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 2, by omega⟩

/- EXACT coefficients of the path-ordered alternating band: the two endpoint
singletons carry letter 0, and row/column pairs have coefficients J. Here r=m-1. -/
def bandWord (r : ℕ) (w : Fin (2 * r + 1) → Letter) : ℂ :=
  (if (parts (w 0)).1 = 0 then 1 else 0) *
  (if (parts (w (Fin.last (2 * r)))).2 = 0 then 1 else 0) *
  ∏ i : Fin r, J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
    J (parts (w (midPos i))).1 (parts (w (rightPos i))).1

/- Ordinary pure position tensor pairing, with no conjugation. -/
def pureWord {n : ℕ} (X : Fin n → Mat) (w : Fin n → Letter) : ℂ :=
  ∏ i, X i (parts (w i)).1 (parts (w i)).2

def entry (a : Letter) : Mat := Matrix.single (parts a).1 (parts a).2 1

def DL (q : ℕ) : Mat →ₗ[ℂ] Mat where
  toFun := Band.D q
  map_add' X Y := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two, add_comm]
    · simp [Band.D, h]
  map_smul' c X := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two]
    · simp [Band.D, h]

def chainML (n p : ℕ) : MultilinearMap ℂ (fun _ : Fin n => Mat) Mat :=
  (MultilinearMap.mkPiAlgebraFin ℂ n Mat).compLinearMap (fun i => DL (p + i.val))

end Saxl.Path

end

end OAI


