-- Prove2me | Definitions.Def_CoDecompFO_Supplement_ExistsFO
-- name    : CoDecompFO_Supplement_ExistsFO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:49:42.490435+00:00
-- url     : https://prove2.me/theorems/ecb92116-5435-4df2-9507-5584e161a9ca
-- title:
--   The quantities of Theorem 4.2: $q=\sum_R\ell^{\mathrm{ar}(R)}$, the time bound, rooted binary co-decompositions
-- statement:
--   For a signature $\sigma$ and $\ell\in\mathbb N$, $q=\sum_{R\in\sigma}\ell^{\mathrm{ar}(R)}$ is the number of atomic statements on $\ell$ points ($0^0=1$). The time bound of Theorem 4.2 is
--
--   $$b(\ell+q)w^{2\ell}2^{2q}+w^{\ell}2^{q}|\varphi| .$$
--
--   A tree co-decomposition is **rooted binary** if, for some root $r$, every node has at most two children. For a list of numbers, its length plus its largest entry is the magnitude a machine word must hold to address and read it.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Theorem 4.2, p.10; B.1, p.53 (PDF pp.12, 55)

import Mathlib
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

variable {σ : Sig}

/-- `q = ∑_{R∈σ} ℓ^{ar(R)}` (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, Theorem 4.2, p.10): the
number of atomic statements on `ℓ` points, so that a hypothesis on `ℓ` points is one of `2^q` (proof of Theorem
4.2, p.16). `0^0 = 1`: a `0`-ary symbol gives one atom. -/
def atomCount (σ : Sig) (ℓ : ℕ) : ℕ := ∑ i : Fin σ.r, ℓ ^ σ.ar i

/-- The running-time expression of Theorem 4.2 (p.10): `b(ℓ+q)w^{2ℓ}2^{2q} + w^ℓ 2^q |φ|`. -/
def bound42 (b w ℓ q len : ℕ) : ℕ := b * (ℓ + q) * w ^ (2 * ℓ) * 2 ^ (2 * q) + w ^ ℓ * 2 ^ q * len

/-- A **rooted binary tree co-decomposition** (Theorem 4.2, p.10; B.1, p.53): for some root `r`, every node has
at most two children (the convention of the published `CoDecompFO.lemma_B_2`). -/
def IsRootedBinary (T : CoDecomp σ) : Prop := ∃ r : Fin T.b, ∀ t, {e | T.IsChildEdge r t e}.ncard ≤ 2

/-- The numbers a word must hold to address and read the input list `l`: its length and its largest entry. -/
def inputMagnitude (l : List ℕ) : ℕ := l.length + l.foldr max 0

end Supplement

end CoDecompFO


