-- Prove2me | Definitions.Def_SubspaceConv_annih
-- name    : SubspaceConv_annih
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:16.127916+00:00
-- url     : https://prove2.me/theorems/ed30121d-4cfb-4cb4-aaea-476759aa9fa4
-- title:
--   Annihilators $B^\circ$ and the value of $\lambda\in B^\circ$ on a coset
-- statement:
--   A vector $\lambda\in\mathbb F_q^d$ is identified with the linear functional $\lambda(x)=\lambda^{\mathsf T}x$. For $B\le\mathbb F_q^d$ the **annihilator** is
--   $$B^\circ=\{\lambda\in\mathbb F_q^d:\ \lambda(B)=0\},$$
--   of dimension $d-\dim B$. For $\lambda\in B^\circ$ the value $\lambda(x+B)=\lambda^{\mathsf T}x$ on a coset does not depend on the representative $x$. If $B\le D$ then $D^\circ\subseteq B^\circ$.
--
--   **Formalization Note** $B^\circ$ is the subtype of vectors with $\lambda\cdot b=0$ for all $b\in B$ (`dotProduct`). The value on cosets is obtained by lifting $x\mapsto\lambda^{\mathsf T}x$ through the quotient map, so no representative is chosen. The helper `annihMono` is the inclusion $D^\circ\subseteq B^\circ$ for $B\le D$.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2, p.10 (λ(x) = λᵀx, B°); §2.1, p.11 (independence of representatives)

import Mathlib

namespace SubspaceConv

/-- The annihilator `B° = {λ ∈ F^d : λ(B) = 0}` of a subspace `B ≤ F^d`, where a vector `λ` acts
as the linear functional `λ(x) = λᵀx` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2, p.10).

**Formalization Note** `λᵀx` is `dotProduct λ x`. Finite for a finite field (a `Fintype` instance
is provided noncomputably). -/
abbrev annih {F : Type*} [Field F] {d : ℕ} (B : Submodule F (Fin d → F)) : Type _ :=
  {lam : Fin d → F // ∀ b ∈ B, dotProduct lam b = 0}

noncomputable instance {F : Type*} [Field F] [Finite F] {d : ℕ} (B : Submodule F (Fin d → F)) :
    Fintype (annih B) :=
  Fintype.ofFinite _

/-- For `B ≤ D`, every `λ ∈ D°` lies in `B°`. -/
def annihMono {F : Type*} [Field F] {d : ℕ} {B D : Submodule F (Fin d → F)} (h : B ≤ D)
    (lam : annih D) : annih B :=
  ⟨lam.1, fun b hb => lam.2 b (h hb)⟩

/-- The value `λ(x + B) = λᵀx` of `λ ∈ B°` on a coset, independent of the representative
because `λ(B) = 0` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, p.11). Defined by lifting `x ↦ λᵀx` through the quotient map. -/
def annihEval {F : Type*} [Field F] {d : ℕ} {B : Submodule F (Fin d → F)} (lam : annih B) :
    (Fin d → F) ⧸ B →ₗ[F] F :=
  B.liftQ (dotProductEquiv F (Fin d) lam.1) (fun b hb => by
    simpa [LinearMap.mem_ker] using lam.2 b hb)

end SubspaceConv


