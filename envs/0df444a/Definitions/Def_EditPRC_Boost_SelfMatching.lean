-- Prove2me | Definitions.Def_EditPRC_Boost_SelfMatching
-- name    : EditPRC_Boost_SelfMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:07:56.7952+00:00
-- url     : https://prove2.me/theorems/dec5871a-41ea-4204-b406-26601df1d7c6
-- title:
--   ε-self-matching strings (Definition 3.13), insertion–deletion processes with provenance, and the unit-cost RAM interface
-- statement:
--   Let $\Gamma$ be a finite alphabet and $s\in\Gamma^n$, with positions $0,\dots,n-1$.
--
--   A **monotone off-diagonal self-matching** of size $t$ is a pair of index sequences $i_1<\dots<i_t$ and $j_1<\dots<j_t$ with $i_\ell\ne j_\ell$ and $s_{i_\ell}=s_{j_\ell}$ for every $\ell$. The string $s$ is **$\varepsilon$-self-matching** (Definition 3.13) if it has no such matching of size $t\ge\varepsilon n$; that is, $s$ has no large off-diagonal common subsequence with itself.
--
--   An **insertion–deletion process** turning $s$ into $s'\in\Gamma^{n'}$ with $d_d$ deletions and $d_i$ insertions is a set $\mathrm{surv}$ of surviving positions of $s$ and an order-preserving map $\mathrm{emb}$ from $\mathrm{surv}$ to positions of $s'$ with $s'_{\mathrm{emb}(i)}=s_i$, where $|\mathrm{surv}|+d_d=n$ and $|\mathrm{surv}|+d_i=n'$. The positions of $s'$ outside the image of $\mathrm{emb}$ hold the inserted symbols, which are arbitrary. The **corresponding symbol** of a surviving $s_i$ is $s'_{\mathrm{emb}(i)}$.
--
--   **RAM interface.** The algorithms of Proposition 3.15 and Theorem 3.16 run on the published unit-cost real RAM `SmaleNinth_RealRAM`. A symbol $a$ is stored as the real $1+\mathrm{index}(a)$. For one string the input memory holds $M[0]=n$ and $M[1+i]=s_i$; for a pair it holds $M[0]=n$, $M[1]=n'$, $M[2+i]=s_i$ and $M[2+n+j]=s'_j$; all other cells are $0$. A program's output matching is read from its final memory: position $i$ of $s$ is matched to position $j$ of $s'$ when $M[-1-i]=j+1$.
--
--   Self-matching strings take the place of synchronization strings in the boost of Theorem 3.12: they let a decoder realign an edited block with its original positions.
--
--   **Formalization Note.** Strings are maps `Fin n → Γ`. The counts $d_d,d_i$ are those of the net effect of the edits on $s$; a symbol inserted and later deleted is not counted.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 25, Definition 3.13, Proposition 3.15 (proof: the off-diagonal LCS dynamic program), Theorem 3.16 (d_i insertions, d_d deletions, corresponding symbols)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false

namespace EditPRC.Boost

/-!
# ε-self-matching strings, insertion/deletion processes, and the unit-cost RAM interface

Gozon, *Edit-Robust Pseudorandom Codes, Watermarks, and Steganography*, STOC 2027 submission
(manuscript sha256 73170029…6b60), p. 25, Definition 3.13, Proposition 3.15 (the
longest-off-diagonal-common-subsequence dynamic program), Theorem 3.16 (`d_i` insertions and
`d_d` deletions; "matched to their corresponding symbol").

* Strings of length `n` are maps `Fin n → Γ` (positions `0, …, n-1`).
* The algorithms of Proposition 3.15 and Theorem 3.16 run on the published unit-cost real RAM
  `SmaleNinth.RAMProgram` (every instruction, including a memory access and a real comparison,
  costs one step; real constants are allowed). Symbols are written into memory as the reals
  `1 + index`, under the fixed enumeration `Fintype.equivFin Γ`.
-/

/-- A **monotone off-diagonal self-matching** of `s` of size `t`: positions
`i_1 < ⋯ < i_t` and `j_1 < ⋯ < j_t` with `i_ℓ ≠ j_ℓ` and `s_{i_ℓ} = s_{j_ℓ}` for all `ℓ`. -/
def IsOffDiagSelfMatching {Γ : Type} {n : ℕ} (s : Fin n → Γ) (t : ℕ) : Prop :=
  ∃ i j : Fin t → Fin n, StrictMono i ∧ StrictMono j ∧ (∀ l, i l ≠ j l) ∧
    ∀ l, s (i l) = s (j l)

/-- **Definition 3.13.** `s ∈ Γ^n` is **ε-self-matching** if it has no monotone off-diagonal
self-matching of any size `t ≥ εn`. -/
def IsSelfMatching {Γ : Type} {n : ℕ} (ε : ℝ) (s : Fin n → Γ) : Prop :=
  ¬ ∃ t : ℕ, ε * n ≤ t ∧ IsOffDiagSelfMatching s t

/-- `s'` arises from `s` by `dd` deletions and `di` insertions, with provenance: the positions
`surv` of `s` survive, `emb` sends them, in order, to the positions of `s'` that carry their
copies, `dd = n − |surv|` and `di = n' − |surv|` (the remaining positions of `s'` are the
inserted symbols, which are arbitrary). -/
def IsInsDel {Γ : Type} {n n' : ℕ} (s : Fin n → Γ) (s' : Fin n' → Γ) (dd di : ℕ)
    (surv : Finset (Fin n)) (emb : Fin n → Fin n') : Prop :=
  surv.card + dd = n ∧ surv.card + di = n' ∧
  (∀ i ∈ surv, ∀ j ∈ surv, i < j → emb i < emb j) ∧
  ∀ i ∈ surv, s' (emb i) = s i

/-- The real written into memory for a symbol: `1 + ` its index. -/
noncomputable def symReal {Γ : Type} [Fintype Γ] (a : Γ) : ℝ :=
  ((Fintype.equivFin Γ a : ℕ) : ℝ) + 1

/-- RAM input memory for one string `s ∈ Γ^n`: `M[0] = n`, `M[1 + i] = symReal (s i)`,
every other cell `0`. -/
noncomputable def ramInput1 {Γ : Type} [Fintype Γ] {n : ℕ} (s : Fin n → Γ) : ℤ → ℝ :=
  fun a =>
    if a = 0 then (n : ℝ)
    else if h : 1 ≤ a ∧ (a - 1).toNat < n then symReal (s ⟨(a - 1).toNat, h.2⟩) else 0

/-- RAM input memory for a pair `s ∈ Γ^n`, `s' ∈ Γ^{n'}`: `M[0] = n`, `M[1] = n'`,
`M[2 + i] = symReal (s i)`, `M[2 + n + j] = symReal (s' j)`, every other cell `0`. -/
noncomputable def ramInput2 {Γ : Type} [Fintype Γ] {n n' : ℕ} (s : Fin n → Γ)
    (s' : Fin n' → Γ) : ℤ → ℝ :=
  fun a =>
    if a = 0 then (n : ℝ)
    else if a = 1 then (n' : ℝ)
    else if h : 2 ≤ a ∧ (a - 2).toNat < n then symReal (s ⟨(a - 2).toNat, h.2⟩)
    else if h' : 2 + (n : ℤ) ≤ a ∧ (a - 2 - n).toNat < n' then
      symReal (s' ⟨(a - 2 - n).toNat, h'.2⟩)
    else 0

/-- The matching read from a RAM configuration: position `i` of `s` is matched to position `j`
of `s'` when the output cell `M[-1-i]` holds `j + 1`. -/
def RAMMatches (cfg : SmaleNinth.RAMConfig) (i j : ℕ) : Prop :=
  cfg.mem (-1 - (i : ℤ)) = (j : ℝ) + 1

end EditPRC.Boost


