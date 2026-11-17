-- Prove2me | Definitions.Def_MonoTestDAG_Supplement_explicitPMRSGraph
-- name    : MonoTestDAG_Supplement_explicitPMRSGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:47:47.181832+00:00
-- url     : https://prove2.me/theorems/c4dec458-3e91-459e-8091-050a02d92921
-- title:
--   The explicit box-and-shift PMRS graph $U(N,k,\alpha)$
-- statement:
--   Fix $N,k\in\mathbb N$ and $\alpha\in(0,1)$, and put $P=\lfloor\alpha N\rfloor$. Each side of the bipartite graph $U(N,k,\alpha)$ is a copy of
--
--   $$[N]^k\times[N^2].$$
--
--   For every nonzero shift $a\in\{0,1,\ldots,P\}^k$, the matching $M_a$ contains exactly the in-box translated pairs
--
--   $$
--   ((x,z)_L,(x+a,z+\lVert a\rVert_2^2)_R).
--   $$
--
--   The edge set of $U(N,k,\alpha)$ is $\bigcup_a M_a$, and the number of indexed shifts is $s=(P+1)^k-1$. This is the explicit graph used by Theorem 4.8.
--
--   **Formalization Note.** The two copies of $[N]^k\times[N^2]$ use `Fin N` coordinates; this is the paper's convention after subtracting one from every coordinate. The left and right sides become disjoint when the published `bipDAG` construction forms their sum. The Lean helper is total on all real $\alpha$ by using the natural floor (zero on negative inputs), but Theorem 4.8 uses only the source domain $0<\alpha<1$. Natural subtraction in $s=(P+1)^k-1$ is exact because $(P+1)^k\ge1$ for every $P,k$.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §4.4.1–4.4.3, pp.21–22 (PDF 23–24)

import Mathlib

namespace MonoTestDAG.Supplement

/-- The paper's integer `P = ⌊αN⌋` in the explicit PMRS construction.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §4.4.2, p.21.

**Formalization Note.** The definition is total on `α : ℝ` by using the natural floor, which is
zero for negative inputs. Theorem 4.8 uses only the source domain `0 < α < 1`, where this is the
ordinary integer floor `⌊αN⌋`. -/
noncomputable def explicitP (N : ℕ) (α : ℝ) : ℕ :=
  ⌊α * (N : ℝ)⌋₊

/-- One side of the explicit bipartite graph: `[N]^k × [N²]`.

**Formalization Note.** `Fin N` is the zero-based copy of the paper's `[N]`; translation preserves
the construction after subtracting one from every coordinate. -/
abbrev ExplicitVertex (N k : ℕ) : Type :=
  (Fin k → Fin N) × Fin (N ^ 2)

/-- The number `s = (P+1)^k - 1` of nonzero shift vectors.

**Formalization Note.** Natural subtraction is exact here for every input because
`1 ≤ (P+1)^k`; at `k=0` both the paper's set of nonzero shifts and this value are empty/zero. -/
noncomputable def explicitS (N k : ℕ) (α : ℝ) : ℕ :=
  (explicitP N α + 1) ^ k - 1

/-- The squared Euclidean norm of a shift vector with coordinates in `{0,…,P}`. -/
def shiftNormSq {k P : ℕ} (a : Fin k → Fin (P + 1)) : ℕ :=
  ∑ i, (a i).val ^ 2

/-- The edge set of the explicit graph `U(N,k,α)` from §4.4. An edge translates the box
coordinate by a nonzero `a ∈ {0,…,P}^k` and the height by `‖a‖²`; translations leaving the box
are absent.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §4.4.1–4.4.3, pp.21–22.

**Formalization Note.** The left and right vertex types are two copies of `ExplicitVertex`; their
disjointness is supplied by `bipDAG`, which orients this finite edge set on a sum type. -/
noncomputable def explicitPMRSGraph (N k : ℕ) (α : ℝ) :
    Finset (ExplicitVertex N k × ExplicitVertex N k) :=
  Finset.univ.filter fun e =>
    ∃ a : Fin k → Fin (explicitP N α + 1),
      (∃ i, (a i).val ≠ 0) ∧
      (∀ i, (e.2.1 i).val = (e.1.1 i).val + (a i).val) ∧
      e.2.2.val = e.1.2.val + shiftNormSq a

end MonoTestDAG.Supplement


