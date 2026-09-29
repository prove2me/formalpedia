-- Prove2me | Definitions.Def_UnramifiedWhittaker_HeckeRecursion
-- name    : UnramifiedWhittaker_HeckeRecursion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/13aa3d83-47a5-5120-b27f-36808a0b1616
-- title:
--   Hecke recursion sequence, torus factor, GL(2) matrices, place embedding
-- statement:
--   Four groups of definitions are made. First, for complex numbers $N$, $\lambda$, $\omega$, the sequence `heckeRecursionSeq` is the function $\mathbb{N} \to \mathbb{C}$ given by $u_0 = 1$, $u_1 = \lambda/N$ and $u_{m+2} = (\lambda u_{m+1} - \omega u_m)/N$ for all $m \ge 0$; since division by zero is zero, for $N = 0$ this reads $u_0 = 1$ and $u_m = 0$ for $m \ge 1$. Second, `torusFactor` extends this to the integers by setting its value at $m$ to be $u_{m}$ when $0 \le m$ (through the truncation $m \mapsto$ `m.toNat`) and $0$ otherwise. Third, over a field $K$, five elements of $\mathrm{GL}_2(K)$ are named, each as an explicit $2\times 2$ matrix together with the verification that its determinant is nonzero: `unipotent x` is $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ for $x \in K$; and, for $\pi \in K$ with $\pi \neq 0$, `diagZ` is $\mathrm{diag}(\pi^{m},1)$ for an integer $m$ (an integer power in $K$), `repSome` is $\begin{pmatrix}\pi&\beta\\0&1\end{pmatrix}$ for $\beta \in K$, `repInf` is $\mathrm{diag}(1,\pi)$ and `scalarPi` is $\mathrm{diag}(\pi,\pi)$. Fourth, for a Dedekind domain $R$ with fraction field $K$ and $v$ a height-one prime of $R$, `placeEmbed` is the group homomorphism $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(\mathbb{A}_{R,K})$ obtained as `localEmbed R K v` followed by `finEmbed R K`: a matrix over the completion $K_v$ is put in the $v$-component and the identity matrix in every other finite component, and the resulting finite-adelic matrix is paired with the identity at the infinite component. No property of these objects is asserted; in particular nothing here links the sequence to a Whittaker function or the matrices to a Hecke operator.
--
--   **Relation to Mathlib.** The $\mathrm{GL}_2$ elements are built from Mathlib's `GeneralLinearGroup.mkOfDetNeZero`; the recursion, the torus factor and the place embedding are the project's own, the last assembled from the project's local and finite adelic embeddings.
--
--   **Where it is used.** These are the local data at a finite place used in the adelic automorphic-forms layer of the argument: the recursion and its extension to the integers record the intended values of an unramified Whittaker function on the diagonal torus, normalised at the base point, while the five matrices are the torus, unipotent, central and coset elements entering the local Hecke operator, transported into $\mathrm{GL}_2$ of the adeles by `placeEmbed`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_UnramifiedWhittaker_HeckeRecursion.lean

import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Matrix

namespace UnramifiedWhittaker

def heckeRecursionSeq (N lam om : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => lam / N
  | m + 2 => (lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m) / N

def torusFactor (N lam om : ℂ) (m : ℤ) : ℂ :=
  if 0 ≤ m then heckeRecursionSeq N lam om m.toNat else 0

section Matrices

variable {K : Type*} [Field K]

def unipotent (x : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [det_fin_two_of])

def diagZ (π : K) (hπ : π ≠ 0) (m : ℤ) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π ^ m, 0; 0, 1] (by simp [det_fin_two_of, zpow_ne_zero m hπ])

def repSome (π : K) (hπ : π ≠ 0) (β : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, β; 0, 1] (by simp [det_fin_two_of, hπ])

def repInf (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, π] (by simp [det_fin_two_of, hπ])

def scalarPi (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, 0; 0, π] (by simp [det_fin_two_of, hπ])

end Matrices

section Adelic

open IsDedekindDomain NumberField AdelicDock

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def placeEmbed (v : HeightOneSpectrum R) :
    GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (AdeleRing R K) :=
  (finEmbed R K).comp (localEmbed R K v)

end Adelic

end UnramifiedWhittaker

end


