-- Prove2me | Definitions.Def_SubspaceConv_crossSub
-- name    : SubspaceConv_crossSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:17.364167+00:00
-- url     : https://prove2.me/theorems/020b1961-2702-4ebd-9bbe-a54a0ee2b775
-- title:
--   The hyperplane $H$, inside subspaces $B\times\{0\}$ and crossing subspaces $U(B,x+B)$
-- statement:
--   The hyperplane cut of §1.2.1. In $\mathbb F_q^{n+1}$ let
--   $$H=\mathbb F_q^{n}\times\{0\}$$
--   be the vectors with last coordinate $0$. For $B\le\mathbb F_q^n$ the **inside subspace** $B\times\{0\}\le H$ consists of the vectors $(b,0)$ with $b\in B$, and for $x\in\mathbb F_q^n$ the **crossing subspace** is
--   $$U(B,x+B)=(B\times\{0\})+\left\langle\binom{x}{1}\right\rangle .$$
--   Lemma 1 shows that every subspace not contained in $H$ is of this form for a unique pair $(B,x+B)$.
--
--   **Formalization Note** The paper's ambient space $\mathbb F_q^n$ with hyperplane $\mathbb F_q^{n-1}\times\{0\}$ is written here as $\mathbb F_q^{n+1}$ with hyperplane $\mathbb F_q^n\times\{0\}$, to avoid natural-number subtraction. Coordinates are 0-based and the distinguished coordinate is the last one. The crossing subspace is defined from a representative $x$; its dependence on the coset only is part of Lemma 1.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.2.1, p.5 (hyperplane H, crossing subspaces X_H); Lemma 1, eq. (3), p.6

import Mathlib

namespace SubspaceConv

/-- The hyperplane `H = F^n × {0}` of `F^{n+1}`: the vectors whose last coordinate is `0`
(Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.2.1, p.5: "Fix the hyperplane H = F_q^{n−1} × {0}").

**Formalization Note** The ambient space is `Fin (n+1) → F` (the paper's `F_q^n` with `n`
replaced by `n+1`, to avoid natural-number subtraction); coordinates are 0-based and the
distinguished coordinate is the last one, `Fin.last n`. -/
def hyperplane (F : Type*) [Field F] (n : ℕ) : Submodule F (Fin (n+1) → F) :=
  LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin (n+1) => F) (Fin.last n))

/-- The subspace `B × {0}` of `F^{n+1}` for `B ≤ F^n`: vectors with last coordinate `0` whose
first `n` coordinates lie in `B` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), eq. (3), p.6). -/
def insideSub {F : Type*} [Field F] {n : ℕ} (B : Submodule F (Fin n → F)) :
    Submodule F (Fin (n+1) → F) :=
  B.comap (LinearMap.funLeft F F (Fin.castSucc : Fin n → Fin (n+1))) ⊓ hyperplane F n

/-- The crossing subspace `U(B, x + B) = (B × {0}) + ⟨(x, 1)⟩` of `F^{n+1}`, for `B ≤ F^n` and
`x ∈ F^n` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), Lemma 1, eq. (3), p.6).

**Formalization Note** The vector `(x, 1)` is `Fin.snoc x 1` (first `n` coordinates `x`, last
coordinate `1`). The definition takes a representative `x`; that the subspace depends only on
the coset `x + B` is part of the milestone `SubspaceConv.lemma_1`. -/
def crossSub {F : Type*} [Field F] {n : ℕ} (B : Submodule F (Fin n → F)) (x : Fin n → F) :
    Submodule F (Fin (n+1) → F) :=
  insideSub B ⊔ Submodule.span F {(Fin.snoc x 1 : Fin (n+1) → F)}

end SubspaceConv


