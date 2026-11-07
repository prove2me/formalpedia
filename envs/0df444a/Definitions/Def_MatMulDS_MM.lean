-- Prove2me | Definitions.Def_MatMulDS_MM
-- name    : MatMulDS_MM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:57.221206+00:00
-- url     : https://prove2.me/theorems/2cf2c839-2791-4551-a6c6-d6d312c21e30
-- title:
--   Bilinear algorithms and $\mathrm{MM}(u,v,w)$
-- statement:
--   A **bilinear algorithm** for multiplying a $u\times v$ matrix by a $v\times w$ matrix consists of linear circuits for each factor, finitely many products of an output of the first with an output of the second, and a linear circuit of these products whose outputs are the entries of the matrix product, correctly on all matrices over $\mathbb F$.
--
--   $\mathrm{MM}(u,v,w)$ is the smallest number of arithmetic operations of such an algorithm, including reading the inputs and writing the output:
--   $$\mathrm{cost}=uv+vw+uw+|\mathrm{enc}_A|+|\mathrm{enc}_B|+r+|\mathrm{dec}|,$$
--   so $\mathrm{MM}(u,v,w)\ge uv+vw+uw$.
--
--   This is the cost that appears in Lemma 4.2, which needs the scheme to be bilinear. The schoolbook algorithm shows that the minimum exists.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MatMulDS_LinCircuit

set_option autoImplicit false

namespace MatMulDS

/-- A bilinear algorithm for multiplying a `u × v` matrix by a `v × w` matrix over `F`: linear circuits
`encA`, `encB` for the two factors, `r` products of a form of `encA` with a form of `encB`, and a linear
circuit `dec` of the products whose output `i * w + j` is entry `(i, j)` of the product.
Source: STOC 2027 submission (held file sha256 6c5a1c16…), §3, p.13; §4.2, p.20 ("The encoding, product,
and decoding parts of a rectangular matrix multiplication circuit together have size MM"). -/
structure BilinearAlgorithm (F : Type) [Field F] (u v w : ℕ) where
  encA : LinCircuit F
  encB : LinCircuit F
  r : ℕ
  a : Fin r → ℕ
  b : Fin r → ℕ
  dec : LinCircuit F
  correct : ∀ (X : Matrix (Fin u) (Fin v) F) (Y : Matrix (Fin v) (Fin w) F) (i : Fin u) (j : Fin w),
    (X * Y) i j = dec.out (productInput encA encB a b (matInput X) (matInput Y)) (i * w + j)

/-- The number of arithmetic operations of a bilinear algorithm, "including reading the inputs and
writing the output" (§3, p.13): `uv + vw + uw` plus the sizes of the three circuits and the number of
products. -/
def BilinearAlgorithm.cost {F : Type} [Field F] {u v w : ℕ} (alg : BilinearAlgorithm F u v w) : ℕ :=
  u * v + v * w + u * w + alg.encA.size + alg.encB.size + alg.r + alg.dec.size

/-- **MM(u, v, w).** "the number of arithmetic operations needed to multiply a u×v matrix by a v×w
matrix by a bilinear algorithm, including reading the inputs and writing the output, so that
MM(u, v, w) ≥ uv + vw + uw" (§3, p.13), over the field `F`.

**Formalization Note** The set of costs is nonempty, by the schoolbook algorithm, so the infimum in `ℕ`
is a minimum and `MM F u v w ≥ uv + vw + uw`. This is checked in the workspace's sanity file. -/
noncomputable def MM (F : Type) [Field F] (u v w : ℕ) : ℕ :=
  sInf {c | ∃ alg : BilinearAlgorithm F u v w, alg.cost = c}

end MatMulDS


