-- Prove2me | Definitions.Def_DenseProdQSAT_Testing_Coordinates
-- name    : DenseProdQSAT_Testing_Coordinates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:32.358196+00:00
-- url     : https://prove2.me/theorems/35283071-faf8-4f3b-91fd-b3d4c6b5fb39
-- title:
--   Finite complex tensor coordinates and normalized product states
-- statement:
--   For a subsystem $S\subseteq V=\{0,\ldots,n-1\}$ and a local dimension $d$, the computational basis is the set of maps $a:S\to\{0,\ldots,d-1\}$. A vector on $S$ assigns a complex coordinate to each basis element. A local pure state $v\in\mathbb C^d$ is normalized when
--
--   $$\sum_{j=0}^{d-1}|v_j|^2=1.$$
--
--   For local amplitudes $\psi_x$, the product vector has coordinate $\prod_{x\in S}\psi_x(a_x)$, including the empty product $1$. The coordinate space carries the usual Euclidean Hermitian structure when used for orthogonality. These definitions provide a common tensor-coordinate interface without restricting the continuum of complex amplitudes. Labels are shifted from the paper's $[n]$ to zero-based finite indices.
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), §1, quantum instance setting; §2, notation, pp. 4–5, p. 2

import Mathlib
set_option autoImplicit false

namespace DenseProdQSAT.Testing

/-- Computational basis of the tensor product over a finite subsystem. -/
abbrev Config {n : ℕ} (d : ℕ) (S : Finset (Fin n)) := S → Fin d
abbrev QVector {n : ℕ} (d : ℕ) (S : Finset (Fin n)) := Config d S → ℂ
abbrev States (n d : ℕ) := Fin n → Fin d → ℂ

def UnitState {d : ℕ} (v : Fin d → ℂ) : Prop :=
  ∑ j, Complex.normSq (v j) = 1

def ProductVector {n d : ℕ} (S : Finset (Fin n)) (ψ : States n d) : QVector d S :=
  fun a => ∏ z : S, ψ z (a z)

end DenseProdQSAT.Testing


