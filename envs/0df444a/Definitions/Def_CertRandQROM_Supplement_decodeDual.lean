-- Prove2me | Definitions.Def_CertRandQROM_Supplement_decodeDual
-- name    : CertRandQROM_Supplement_decodeDual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:41:42.24048+00:00
-- url     : https://prove2.me/theorems/4b62a71f-89bd-4f08-ac50-2cf1c17e1b7f
-- title:
--   The dual decoder $\mathrm{Decode}_{C^\perp}$ at radius $\tau=\lfloor (k+1)/2\rfloor$
-- statement:
--   For a word $e\in\Sigma^n$, $\Sigma=\mathbb F_q^m$, let $\mathrm{hw}(e)$ be its Hamming weight as a vector of $\mathbb F_q^{nm}$ (the number of nonzero field coordinates), and let $\tau=\lfloor (k+1)/2\rfloor$ for the degree parameter $k$ of the code. The decoder of the dual code is
--
--   $$
--   \mathrm{Decode}_{C^\perp}(z)=\begin{cases}x&\text{if } x\in C^\perp \text{ and } \mathrm{hw}(z-x)\le\tau,\\ 0&\text{if no such } x \text{ exists.}\end{cases}
--   $$
--
--   This is the paper's decoder: it runs the unique decoder of the (generalized Reed–Solomon) dual code with decoding radius $\tau$ and returns $0$ when that decoder fails. It is the map $F$ applied by the unitary $U_{\mathrm{decode}}$ of the honest prover.
--
--   **Formalization Note** `unfoldWeight` is $\mathrm{hw}$ and `decRadius k` is $\tau$. When several dual codewords lie within distance $\tau$ the definition picks one by choice; for the codes $C_\lambda$ of §5.2 this never happens, because $d_{\min}(C^\perp)=k+2>2\tau$. No property of the decoder is assumed in any statement.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §5.1, GRSUniqueDecode, p.22 (PDF p.24); proof of Lemma 5.2, item 2, definition of Decode_{C⊥}, pp.25–26 (PDF pp.27–28)

import Mathlib
import Definitions.Def_CertRandQROM_Supplement_dualCode

set_option autoImplicit false

namespace CertRandQROM.Supplement

open Classical in
/-- The **unfolded Hamming weight** `hw(e)` of a folded word `e ∈ Σ^n`, `Σ = F_q^m`: the number
of nonzero field coordinates of `e` regarded as an element of `F_q^{N}`, `N = n·m`
(proof of Lemma 5.2, item 2, p.25 of arXiv:2608.31112, sha256 b75095a2…: "hw(e) denotes its
Hamming weight in `F_q^N`"). -/
noncomputable def unfoldWeight {K : Type} [Field K] {n m : ℕ} (e : Fin n → Fin m → K) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin m => e p.1 p.2 ≠ 0).card

/-- The decoding radius `τ = ⌊(k + 1)/2⌋` of `Decode_{C⊥}` (p.25 of arXiv:2608.31112). -/
def decRadius (k : ℕ) : ℕ := (k + 1) / 2

open Classical in
/-- **The dual decoder `Decode_{C⊥}`** (proof of Lemma 5.2, item 2, p.25 of Coladangelo et al.,
arXiv:2608.31112, sha256 b75095a2…): on input `z ∈ Σ^n`, run the unique decoder of `C⊥` with
decoding radius `τ`; if it returns a codeword of `C⊥` (a codeword `x ∈ C⊥` with
`hw(z − x) ≤ τ`, unfolded weight), return it, otherwise return `0`.

**Formalization Note** The specification of `GRSUniqueDecode` (p.22) is: return the codeword
within distance `τ` if one exists, else `⊥`; `Decode` maps `⊥` to `0`. The codeword is chosen
with `Classical.choose`; for the code `C_λ` it is unique, because `d_min(C⊥) = k + 2 > 2τ`
(p.26), so the choice is immaterial there. The statement of Theorem 6.6 applies this function
with `τ = decRadius k`. -/
noncomputable def decodeDual {K : Type} [Field K] [Fintype K] [DecidableEq K] {n m : ℕ}
    (C : Finset (Fin n → Fin m → K)) (τ : ℕ) (z : Fin n → Fin m → K) : Fin n → Fin m → K :=
  if h : ∃ x ∈ dualCode C, unfoldWeight (z - x) ≤ τ then h.choose else 0

end CertRandQROM.Supplement


