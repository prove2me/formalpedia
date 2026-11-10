-- Prove2me | Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
-- name    : TensorRankN2M_ThreeTwoM_Decomposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:15:36.890313+00:00
-- url     : https://prove2.me/theorems/a14ae81c-01b5-45a7-b11a-e7af3668c6e8
-- title:
--   R-rank decompositions of the ⟨k,l,m⟩ matrix multiplication tensor and the tensor rank R(⟨k,l,m⟩) (§1)
-- statement:
--   Let $\mathbb F$ be a field and $k,l,m,R$ natural numbers. An **$R$-rank decomposition** of the $\langle k,l,m\rangle$ matrix multiplication tensor over $\mathbb F$ is a list of $\mathbb F$-linear forms $\alpha_r:\mathbb F^{k\times l}\to\mathbb F$, $\beta_r:\mathbb F^{l\times m}\to\mathbb F$ and matrices $C_r\in\mathbb F^{k\times m}$, for $0\le r<R$, such that for all $A\in\mathbb F^{k\times l}$ and $B\in\mathbb F^{l\times m}$
--   $$AB=\sum_{r} \alpha_r(A)\,\beta_r(B)\,C_r .$$
--   The matrices $C_r$ are arbitrary (zero is allowed). The **rank** $R(\langle k,l,m\rangle)$ over $\mathbb F$ is the smallest $R$ for which such a decomposition exists. A decomposition always exists (the $klm$ products $A_{ij}B_{jt}$ give one with $R=klm$), so the minimum is attained; the rank may depend on $\mathbb F$.
--
--   Rank decompositions are the objects behind fast matrix multiplication: an $R$-rank decomposition of $\langle k,l,m\rangle$ yields a recursive algorithm for large matrix products, so lower bounds on $R(\langle k,l,m\rangle)$ limit what such algorithms can achieve.
--
--   **Formalization Note.** `Decomposition 𝔽 k l m R` bundles `α r`, `β r` (as `→ₗ[𝔽] 𝔽`), `C r` (as `Matrix (Fin k) (Fin m) 𝔽`), indexed by `r : Fin R`, and the decomposition equation. `tensorRank 𝔽 k l m` is `sInf` of the set of `R` admitting a decomposition; that set is nonempty, so `sInf` is its minimum.
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 2, §1

import Mathlib

/-!
# Rank decompositions of the ⟨k,l,m⟩ matrix multiplication tensor and tensor rank

Jason Yang, *New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra*,
STOC 2027 submission (manuscript of October 2026), p. 2, §1.

An `R`-rank decomposition of ⟨k,l,m⟩ over a field `𝔽` is a list of linear forms
`α r : 𝔽^{k×l} → 𝔽`, `β r : 𝔽^{l×m} → 𝔽` and matrices `C r ∈ 𝔽^{k×m}`, `r : Fin R`
(the paper's `0 ≤ r < R`), such that `A * B = ∑ r, α r A * β r B • C r` for all `A`, `B`.
The rank `R(⟨k,l,m⟩)` is the smallest `R` for which a decomposition exists.
-/

namespace TensorRankN2M.ThreeTwoM

/-- An `R`-rank decomposition of the ⟨k,l,m⟩ matrix multiplication tensor over `𝔽` (p. 2). -/
structure Decomposition (𝔽 : Type*) [Field 𝔽] (k l m R : ℕ) where
  /-- The linear forms `α_r : 𝔽^{k×l} → 𝔽`. -/
  α : Fin R → (Matrix (Fin k) (Fin l) 𝔽 →ₗ[𝔽] 𝔽)
  /-- The linear forms `β_r : 𝔽^{l×m} → 𝔽`. -/
  β : Fin R → (Matrix (Fin l) (Fin m) 𝔽 →ₗ[𝔽] 𝔽)
  /-- The matrices `C_r ∈ 𝔽^{k×m}` (arbitrary, zero allowed). -/
  C : Fin R → Matrix (Fin k) (Fin m) 𝔽
  /-- The decomposition equation `AB = ∑_r α_r(A) β_r(B) C_r`. -/
  eq : ∀ (A : Matrix (Fin k) (Fin l) 𝔽) (B : Matrix (Fin l) (Fin m) 𝔽),
    A * B = ∑ r, (α r A * β r B) • C r

/-- The rank `R(⟨k,l,m⟩)` over `𝔽`: the smallest `R` such that an `R`-rank decomposition of
⟨k,l,m⟩ exists (p. 2). The set is nonempty (`R = klm` works), so this is a true minimum. -/
noncomputable def tensorRank (𝔽 : Type*) [Field 𝔽] (k l m : ℕ) : ℕ :=
  sInf {R : ℕ | Nonempty (Decomposition 𝔽 k l m R)}

end TensorRankN2M.ThreeTwoM


