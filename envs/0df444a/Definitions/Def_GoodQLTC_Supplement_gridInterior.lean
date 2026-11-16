-- Prove2me | Definitions.Def_GoodQLTC_Supplement_gridInterior
-- name    : GoodQLTC_Supplement_gridInterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:00:02.876207+00:00
-- url     : https://prove2.me/theorems/80c9507e-4078-4ba7-bc86-3eec8801d919
-- title:
--   Norm-one grids, $\ell$-closure and interior (Definition 12.1)
-- statement:
--   Let $k$ be a field and $q_1,\dots,q_r$ positive integers. The **norm-one grid** is
--   $$\Omega:=\prod_{i=1}^r\Omega_i\subseteq k^r,\qquad \Omega_i:=\{z\in k: z^{q_i+1}=1\}.$$
--   For $z\in\Omega$ its $i$-th **coordinate line** is $L_i(z):=\{x\in\Omega: x_j=z_j\text{ for all }j\ne i\}$. For an integer $\ell\ge0$ let $\mathcal P_\ell:=\{P\in k[X_1,\dots,X_r]:\deg_{X_i}P\le\ell\text{ for every }i\}$. For $W\subseteq\Omega$,
--   $$\mathrm{cl}_\ell(W):=\{z\in\Omega:\ P(z)=0\text{ for every }P\in\mathcal P_\ell\text{ with }P|_W=0\}.$$
--   A set $T\subseteq\Omega$ is **$\ell$-closed** if $\mathrm{cl}_\ell(T)=T$, and its **interior** is
--   $$T^\circ:=\{z\in T: L_i(z)\not\subseteq T\text{ for every }i\in[r]\}.$$
--
--   These are the objects of the interpolation theorem (Theorem 12.2) behind the uniform product expansion of Reed–Solomon codes.
--
--   **Formalization Note** $k[X]$ is `MvPolynomial (Fin r) k`; $\deg_{X_i}$ is the degree in the single variable $X_i$ (`degreeOf`), not the total degree.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §12, p.39 (PDF 42): Ω_i, Ω, L_i(z), P_ℓ, Definition 12.1

import Mathlib

namespace GoodQLTC.Supplement

/-- The **norm-one grid** `Ω := ∏_{i=1}^r Ω_i`, `Ω_i := {z ∈ k : z^{q_i+1} = 1}`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §12, p.39, as a subset of `k^r`.

**Formalization Note.** Points of `k^r` are functions `Fin r → k`. -/
def normOneGrid {k : Type} [Field k] {r : ℕ} (q : Fin r → ℕ) : Set (Fin r → k) :=
  {z | ∀ i, z i ^ (q i + 1) = 1}

/-- The `i`-th **coordinate line** `L_i(z) := {x ∈ Ω : x_j = z_j for all j ≠ i}` through `z`
(arXiv:2609.20780, §12, p.39). -/
def coordLine {k : Type} [Field k] {r : ℕ} (q : Fin r → ℕ) (z : Fin r → k) (i : Fin r) :
    Set (Fin r → k) :=
  {x | x ∈ normOneGrid q ∧ ∀ j, j ≠ i → x j = z j}

/-- The **`ℓ`-closure** `cl_ℓ(W) := {z ∈ Ω : P(z) = 0 for every P ∈ P_ℓ with P|_W = 0}`,
`P_ℓ := {P ∈ k[X] : deg_{X_i} P ≤ ℓ for every i}`, Gay–Jeronimo, arXiv:2609.20780 (held version),
Definition 12.1, p.39.

**Formalization Note.** `k[X]` is `MvPolynomial (Fin r) k`; `deg_{X_i}` is `MvPolynomial.degreeOf i`
(degree in each variable separately, not total degree). -/
def gridClosure {k : Type} [Field k] {r : ℕ} (q : Fin r → ℕ) (ℓ : ℕ) (W : Set (Fin r → k)) :
    Set (Fin r → k) :=
  {z | z ∈ normOneGrid q ∧ ∀ P : MvPolynomial (Fin r) k, (∀ i, P.degreeOf i ≤ ℓ) →
    (∀ w ∈ W, MvPolynomial.eval w P = 0) → MvPolynomial.eval z P = 0}

/-- `T ⊆ Ω` is **`ℓ`-closed** if `cl_ℓ(T) = T` (arXiv:2609.20780, Definition 12.1, p.39). -/
def IsGridClosed {k : Type} [Field k] {r : ℕ} (q : Fin r → ℕ) (ℓ : ℕ) (T : Set (Fin r → k)) :
    Prop :=
  gridClosure q ℓ T = T

/-- The **interior** `T° := {z ∈ T : L_i(z) ⊄ T for every i ∈ [r]}` (arXiv:2609.20780,
Definition 12.1, p.39). -/
def gridInterior {k : Type} [Field k] {r : ℕ} (q : Fin r → ℕ) (T : Set (Fin r → k)) :
    Set (Fin r → k) :=
  {z | z ∈ T ∧ ∀ i, ¬ coordLine q z i ⊆ T}

end GoodQLTC.Supplement


