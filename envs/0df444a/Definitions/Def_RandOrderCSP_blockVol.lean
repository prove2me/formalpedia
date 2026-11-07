-- Prove2me | Definitions.Def_RandOrderCSP_blockVol
-- name    : RandOrderCSP_blockVol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:16.715206+00:00
-- url     : https://prove2.me/theorems/95b3fa95-a3a8-4dd6-b9f1-3babb49ad48b
-- title:
--   Block supports, block volume, singleton-free sets and the block potential
-- statement:
--   For a partition $\mathcal P$ of a finite set $U$ and $T\subseteq U$: $\mathcal P(T)$ is the set of blocks meeting $T$, $\mathcal P^j(T)$ the blocks $B$ with $|B\cap T|=j$, and $\mathrm{vol}(\mathcal P(T))=\sum_{B\in\mathcal P(T)}|B|$. $T$ is **$\mathcal P$-singleton-free** if $\mathcal P^1(T)=\emptyset$, and $\mathrm{SF}_{\mathcal P}(t,\ell)$ is the family of singleton-free $T$ with $|T|=t$ and $|\mathcal P(T)|=\ell$. For $z\ge1$ and $\ell\ge0$ the **block potential** is
--
--   $$\Psi_\ell(\mathcal P;z)=\sum_{\mathcal T\subseteq\mathcal P^{\ge2},\,|\mathcal T|=\ell}\ \prod_{B\in\mathcal T}z^{|B|}.$$
--
--   These quantities index the Fourier estimates of the lower bound.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3, pp.10–11

import Mathlib

namespace RandOrderCSP

variable {U : Type} [Fintype U] [DecidableEq U]

/-- `𝒫(T)`: the blocks of the partition `𝒫` that meet `T` (p.10). -/
def blockSupport (P : Finpartition (Finset.univ : Finset U)) (T : Finset U) :
    Finset (Finset U) :=
  P.parts.filter fun B => (B ∩ T).Nonempty

/-- `𝒫^j(T)`: the blocks `B` of `𝒫` with `|B ∩ T| = j` (p.10). -/
def blockExact (P : Finpartition (Finset.univ : Finset U)) (j : ℕ) (T : Finset U) :
    Finset (Finset U) :=
  P.parts.filter fun B => (B ∩ T).card = j

/-- **Block volume** (§3, p.11).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.11: "The block volume of T is
vol(𝒫(T)) := ∑_{B∈𝒫(T)} |B|."

**Formalization Note.** A partition of a finite set `U` is a `Finpartition` of `Finset.univ`, whose
blocks are nonempty. This module also holds the block supports `blockSupport`, `blockExact`, the
families (3.1) and the block potential (3.2). -/
def blockVol (P : Finpartition (Finset.univ : Finset U)) (T : Finset U) : ℕ :=
  ∑ B ∈ blockSupport P T, B.card

/-- `T ∈ SF_𝒫` (3.1), p.11: `T` is `𝒫`-singleton-free, i.e. `𝒫¹(T) = ∅`. -/
abbrev IsSF (P : Finpartition (Finset.univ : Finset U)) (T : Finset U) : Prop :=
  blockExact P 1 T = ∅

/-- `T ∈ SF_𝒫(t, ℓ)` (3.1), p.11: `T` is `𝒫`-singleton-free, `|T| = t` and `|𝒫(T)| = ℓ`. -/
abbrev IsSFtl (P : Finpartition (Finset.univ : Finset U)) (t ℓ : ℕ) (T : Finset U) : Prop :=
  IsSF P T ∧ T.card = t ∧ (blockSupport P T).card = ℓ

/-- The block potential `Ψ_ℓ(𝒫; z) := ∑_{𝒯 ⊆ 𝒫^{≥2}, |𝒯| = ℓ} ∏_{B∈𝒯} z^{|B|}` (3.2), p.11. -/
def blockPotential (P : Finpartition (Finset.univ : Finset U)) (z : ℝ) (ℓ : ℕ) : ℝ :=
  ∑ T ∈ (P.parts.filter fun B => 2 ≤ B.card).powersetCard ℓ, ∏ B ∈ T, z ^ B.card

end RandOrderCSP


