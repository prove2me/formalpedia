-- Prove2me | Definitions.Def_QubitTracking_cosetWinProb
-- name    : QubitTracking_cosetWinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:19.909228+00:00
-- url     : https://prove2.me/theorems/220df17e-2f4e-4de8-9dbe-a666ee19fbd1
-- title:
--   Canonical coset representatives and the coset monogamy game of Theorem 6.2
-- statement:
--   Let $A\le\mathbb F_2^n$ be spanned by the first $k$ columns of $U\in GL_n(\mathbb F_2)$. The canonical representatives are $\mathsf{Can}_A(s)=Uw$, where $w$ is $U^{-1}s$ with its first $k$ coordinates set to $0$, and $\mathsf{Can}_{A^\perp}(s')=U^{-t}w'$, where $w'$ is $U^ts'$ with its last $n-k$ coordinates set to $0$; $\mathsf{CS}(A)$ and $\mathsf{CS}(A^\perp)$ are their images. The coset state is $|A_{s,t}\rangle=|A|^{-1/2}\sum_{a\in A}(-1)^{\langle a,t\rangle}|a+s\rangle$.
--
--   In the coset monogamy game, $U$ is uniform, $A$ is spanned by its first $n/2$ columns, $s$ is uniform in $\mathsf{CS}(A)$ and $t$ uniform in $\mathsf{CS}(A^\perp)$. $\mathcal A_M$ maps $|A_{s,t}\rangle$ to registers $\mathbf L\mathbf R$ by an isometry $V$; for uniform $r_L,r_R$, $\mathcal A_L$ measures a two-outcome measurement $P_L(U,r_L)$ on $\mathbf L$ (outcome $b^l_0$) and $\mathcal A_R$ measures $P_R(U,r_R)$ on $\mathbf R$ (outcome $b^r_1$). The adversary wins iff $b^l_0\oplus b^r_1=\langle r_L,s\rangle\oplus\langle r_R,t\rangle$.
--
--   **Formalization Note** A general channel $\mathbf M\to\mathbf L\mathbf R$ is an isometry followed by discarding an environment, which the adversary may hand to $\mathcal A_L$; isometries therefore cover every adversary.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Remark 4.1 (p.26), Theorem 6.2 and Remark 6.3 (pp.33–34)

import Definitions.Def_QubitTracking_anchorVec

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-! Canonical coset representatives (Remark 4.1) and the coset monogamy game of Theorem 6.2.

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Remark 4.1 (p.26), Theorem 6.2 and Remark 6.3
(pp.33–34). -/

/-- `Can_A(s)` (Remark 4.1, p.26) for the subspace `A ≤ 𝔽₂^n` spanned by the first `k` columns of
the change of basis `U` (column indices `C = {0, …, k−1}`): `U w`, where `w` is `U^{-1} s` with its
coordinates in `C` replaced by zeros. -/
def canA {n : ℕ} (U : GL (Fin n) (ZMod 2)) (k : ℕ) (s : Bits (Fin n)) : Bits (Fin n) :=
  (U : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
    fun i => if (i : ℕ) < k then 0 else ((↑U⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ s) i

/-- `Can_{A^⊥}(s′)` (Remark 4.1, p.26): `U^{-t} w′`, where `w′` is `U^t s′` with its coordinates not
in `C` replaced by zeros, and `U^{-t} = (U^t)^{-1}`. -/
def canPerp {n : ℕ} (U : GL (Fin n) (ZMod 2)) (k : ℕ) (s' : Bits (Fin n)) : Bits (Fin n) :=
  ((↑U⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ
    fun i => if (i : ℕ) < k then ((U : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ s') i else 0

/-- `CS(A) = {Can_A(s) : s ∈ 𝔽₂^n}` (Remark 4.1, p.26). -/
noncomputable def csA {n : ℕ} (U : GL (Fin n) (ZMod 2)) (k : ℕ) : Finset (Bits (Fin n)) :=
  Finset.univ.image (canA U k)

/-- `CS(A^⊥) = {Can_{A^⊥}(s′) : s′ ∈ 𝔽₂^n}` (Remark 4.1, p.26). -/
noncomputable def csPerp {n : ℕ} (U : GL (Fin n) (ZMod 2)) (k : ℕ) : Finset (Bits (Fin n)) :=
  Finset.univ.image (canPerp U k)

open Classical in
/-- The coset state `|A_{s,t}⟩ = |A|^{-1/2} ∑_{a ∈ A} (−1)^{⟨a,t⟩} |a + s⟩` (Theorem 6.2, p.33): the
amplitude of `|z⟩` is `|A|^{-1/2} (−1)^{⟨z − s, t⟩}` if `z − s ∈ A`, else `0`. -/
noncomputable def cosetState {n : ℕ} (A : Submodule (ZMod 2) (Bits (Fin n))) (s t : Bits (Fin n)) :
    Bits (Fin n) → ℂ :=
  fun z => if z - s ∈ A then ((Real.sqrt (Nat.card A : ℝ) : ℂ))⁻¹ * sgn ((z - s) ⬝ᵥ t) else 0

/-- The effect of a two-outcome measurement for outcome `b`: `P` for `b = 1`, `1 − P` for
`b = 0`. -/
def outcomeEffect {β : Type} [Fintype β] [DecidableEq β] (P : Matrix β β ℂ) (b : ZMod 2) :
    Matrix β β ℂ :=
  if b = 1 then P else 1 - P

open Classical in
/-- **`Pr[CosetMonogamy(𝒜, 1^λ) = 1]`** (Theorem 6.2, pp.33–34) for `n` qubits and the adversary
`𝒜 = (𝒜_M, 𝒜_L, 𝒜_R)` given by an isometry `V` from the `n`-qubit register `𝐌` to `𝐋 ⊗ 𝐑` and two-outcome
measurements `P_L(U, r_L)` on `𝐋` and `P_R(U, r_R)` on `𝐑`:
1. `U` uniform in `GL_n(𝔽₂)`, `A` the span of its first `n/2` columns, `s` uniform in `CS(A)`, `t`
   uniform in `CS(A^⊥)`; `𝒜_M` receives `|A_{s,t}⟩`;
2. `𝒜_M` maps it to `𝐋𝐑` by `V`;
3. `r_L, r_R` uniform in `𝔽₂^n`; `𝒜_L` measures `P_L(U, r_L)` (outcome `b^l_0`), `𝒜_R` measures
   `P_R(U, r_R)` (outcome `b^r_1`); the adversary wins iff `b^l_0 ⊕ b^r_1 = ⟨r_L, s⟩ ⊕ ⟨r_R, t⟩`.

**Formalization Note** An arbitrary channel `𝐌 → 𝐋𝐑` is an isometry followed by discarding an
environment, which the adversary may as well hand to `𝒜_L`; so isometries cover every adversary. -/
noncomputable def cosetWinProb (n : ℕ) {L R : Type} [Fintype L] [DecidableEq L] [Fintype R]
    [DecidableEq R] (V : Matrix (L × R) (Bits (Fin n)) ℂ)
    (PL : GL (Fin n) (ZMod 2) → Bits (Fin n) → Matrix L L ℂ)
    (PR : GL (Fin n) (ZMod 2) → Bits (Fin n) → Matrix R R ℂ) : ℝ :=
  avg fun U : GL (Fin n) (ZMod 2) =>
    avgOn (csA U (n / 2)) fun s =>
      avgOn (csPerp U (n / 2)) fun t =>
        avg fun r : Bits (Fin n) × Bits (Fin n) =>
          ∑ bl : ZMod 2, ∑ br : ZMod 2,
            if bl + br = r.1 ⬝ᵥ s + r.2 ⬝ᵥ t then
              (inner' (V *ᵥ cosetState (colSpan U (n / 2)) s t)
                (kroneckerMap (· * ·) (outcomeEffect (PL U r.1) bl) (outcomeEffect (PR U r.2) br) *ᵥ
                  (V *ᵥ cosetState (colSpan U (n / 2)) s t))).re
            else 0

end QubitTracking


