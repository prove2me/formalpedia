-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
-- name    : OAI_RepresentationTheory_Saxl_BandPairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:06:51.113248+00:00
-- url     : https://prove2.me/theorems/c651f110-6111-4b13-8726-ea8aad7da8d5
-- title:
--   Conjugation by $Q$ and the matrix-chain functional on four-letter words
-- statement:
--   Two linear maps on $2\times 2$ complex matrices, used to evaluate contractions of word vectors as matrix entries.
--
--   Let $\mathrm{Mat}=\mathbb{C}^{2\times 2}$ and $[n]=\{0,\dots,n-1\}$. For $q\in\mathbb{N}$ let $D_q(X)=\operatorname{adj}(X)$ when $q$ is even and $D_q(X)=X$ when $q$ is odd, with $\operatorname{adj}\begin{pmatrix}a&b\\ c&d\end{pmatrix}=\begin{pmatrix}d&-b\\ -c&a\end{pmatrix}$. A letter $a\in[4]$ is identified with the pair $(a_1,a_2)\in[2]\times[2]$ such that $a=2a_1+a_2$, and $E_a$ is the matrix unit with entry $1$ in position $(a_1,a_2)$ and $0$ elsewhere. Let $M_{n,4}$ be the space of functions $x:[4]^{[n]}\to\mathbb{C}$ on words $w=(w_0,\dots,w_{n-1})$ of length $n$ over $[4]$.
--
--   1. **Conjugation by $Q$.** With
--   $$
--   Q=\begin{pmatrix}1&1\\ 1&2\end{pmatrix},\qquad Q^{-1}=\begin{pmatrix}2&-1\\ -1&1\end{pmatrix},
--   $$
--   the map $\mathrm{conj}:\mathrm{Mat}\to\mathrm{Mat}$, $X\mapsto QXQ^{-1}$, as a $\mathbb{C}$-linear map.
--
--   2. **Chain functional.** For $n,p\in\mathbb{N}$, the linear map $\Phi_{n,p}:M_{n,4}\to\mathrm{Mat}$ given by
--   $$
--   \Phi_{n,p}(x)=\sum_{w\in[4]^{[n]}}x(w)\;D_{p}(E_{w_0})\,D_{p+1}(E_{w_1})\cdots D_{p+n-1}(E_{w_{n-1}}),
--   $$
--   the product being ordered from left to right. Since each $D_q$ is linear and the ordered product is multilinear, $\Phi_{n,p}$ is the linear extension of $(X_0,\dots,X_{n-1})\mapsto D_p(X_0)\cdots D_{p+n-1}(X_{n-1})$ when $M_{n,4}$ is identified with $\mathrm{Mat}^{\otimes n}$ through matrix entries: on the vector $w\mapsto\prod_i (X_i)_{(w_i)_1,(w_i)_2}$ it returns exactly this product.
--
--   Since $Q$ has determinant one, conjugation by $Q$ is an algebra automorphism of $\mathrm{Mat}$ that commutes with every $D_q$, so it can be pulled through ordered chain products. The $(0,0)$ entry of the chain functional with offset $p=1$ on words of odd length $2r+1$ computes, up to the sign $(-1)^r$, the coordinate pairing with a fixed alternating path vector. Together these reduce the non-vanishing of certain polytabloid contractions to explicit $2\times 2$ matrix computations.
--
--   **Formalization Note** The maps are `Saxl.Band.conjugation`, defined as `Q * X * Qinv` with the explicit matrix `Qinv` (that it inverts `Q` is proved separately), and `Saxl.Path.chainFunctional n p`, which uses the multilinear map `chainML n p` obtained from `MultilinearMap.mkPiAlgebraFin` composed with the linear maps `DL (p + i)` (that is, $D_{p+i}$). Letters are `Fin 4`, decoded by `parts = finProdFinEquiv.symm`, and $E_a$ is `entry a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandPairing.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandPairing.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

def conjugation : Mat →ₗ[ℂ] Mat where
  toFun X := Q * X * Qinv
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

end Saxl.Band
namespace Saxl.Path

def chainFunctional (n p : ℕ) : WordSpace n 4 →ₗ[ℂ] Mat where
  toFun x := ∑ w : Fin n → Fin 4, x w • chainML n p (fun i => entry (w i))
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]

/- The actual complex Specht modules with at most four rows occur in the
specified two-layer alternating path cyclic module. -/
end Saxl.Path

namespace Saxl.PathLayer

end Saxl.PathLayer

end

end OAI


