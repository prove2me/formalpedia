-- Prove2me | Definitions.Def_SuccinctArgOWF_Kilian_Blocks
-- name    : SuccinctArgOWF_Kilian_Blocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:06.987148+00:00
-- url     : https://prove2.me/theorems/b83ff93b-b2e0-4b94-928b-38fa6ad45448
-- title:
--   Construction 6.1 — parallel blocks with shared receiver coins
-- statement:
--   Let $\widetilde{\mathrm{Com}}$ be an $\ell$-round public-coin commitment for $n$-bit messages and $N$ a multiple of $n$. For $m\in\{0,1\}^N$ and $i\in[N/n]$ let $m^{(i)}=m_{(i-1)n+1}\cdots m_{in}$ be the $i$-th block.
--
--   **Construction 6.1.** The sender commits to every block with $\widetilde{\mathrm{Com}}$, using the same receiver coins $\rho=(r_1,\dots,r_\ell)$ for all blocks: in round $j$ it sends $y_j=(y_j^{(i)})_{i\in[N/n]}$ with $(y_j^{(i)},\widetilde{\mathrm{state}}^{(i)}_j)=\widetilde S_j(\widetilde{\mathrm{state}}^{(i)}_{j-1},r_j)$. For an interval $I$ let
--
--   $$B(I)=\{\lceil k/n\rceil : k\in I\}\subseteq[N/n].$$
--
--   $\mathrm{Open}(\mathrm{state},I)=(m^{(i)},\widetilde{\mathrm{Open}}(\widetilde{\mathrm{state}}^{(i)}_\ell))_{i\in B(I)}$, and $\mathrm{Ver}(\rho,\tau,I,v,\pi)$ parses $\pi=(u^{(i)},\tilde\pi^{(i)})_{i\in B(I)}$ with $u^{(i)}\in\{0,1\}^n$ and accepts iff the $(k-(i-1)n)$-th bit of $u^{(i)}$ with $i=\lceil k/n\rceil$ equals $v_k$ for every $k\in I$, and $\widetilde{\mathrm{Ver}}(\rho,\tau^{(i)},u^{(i)},\tilde\pi^{(i)})=1$ for every $i\in B(I)$. The map $J(I)=\{(a-1)\tilde d+1,\dots,b\tilde d\}$, where $B(I)=\{a,\dots,b\}$, is the interval of Theorem 6.2.
--
--   This is the inner scheme of the vector commitment of Corollary 6.3.
--
--   **Formalization Note** The tuple $y_j$ is the plain concatenation of the block messages when they all have the same length (in particular when $\widetilde{\mathrm{Com}}$ sends $\tilde d$ bits per round, so $y_j\in\{0,1\}^{N\tilde d/n}$), and otherwise a self-delimiting code of the tuple whose length is $\not\equiv0\pmod{N/n}$, so that the receiver recovers the tuple in both cases.
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Construction 6.1 and Theorem 6.2, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Commit

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-! # Parallel blocks with shared receiver coins (Construction 6.1) -/

/-- The tuple `(y^{(1)}, …, y^{(B)})` of the block messages of one round, as one string: the plain
concatenation when all entries have the same length (in particular when the base scheme sends `d̃`
bits per round) or when `B ≤ 1`, and otherwise the self-delimiting code padded with zeros to a length
`≡ 1 (mod B)`, so that `tupleDec` recovers the tuple in both cases. -/
def tupleEnc (B : ℕ) (ys : List Str) : Str :=
  if B ≤ 1 ∨ ∀ y ∈ ys, y.length = (ys.headD []).length then ys.flatten
  else encList ys ++ List.replicate ((B + 1 - (encList ys).length % B) % B) false

/-- Decoding of `tupleEnc B` into `B` block messages. -/
def tupleDec (B : ℕ) (y : Str) : List Str :=
  if B ≤ 1 then [y]
  else if y.length % B = 0 then
    (List.range B).map fun i => (y.drop (i * (y.length / B))).take (y.length / B)
  else ((decList y).getD []).take B

/-- The `i`-th block `m^{(i)} = m_{(i−1)n+1} ⋯ m_{in}` of `m` (blocks indexed from `1`). -/
def block (n : ℕ) (m : Str) (i : ℕ) : Str := sub m ((i - 1) * n + 1) (i * n)

/-- `B(I) = {⌈k/n⌉ : k ∈ I}` for `I = {a, …, b}`, as the list `⌈a/n⌉, …, ⌈b/n⌉`. -/
def blocksOf (n a b : ℕ) : List ℕ :=
  List.range' ((a + n - 1) / n) ((b + n - 1) / n + 1 - (a + n - 1) / n)

open Classical in
/-- Construction 6.1 (p.19): the sender commits to every block `m^{(i)}`, `i ∈ [N/n]`, with the base
scheme `C̃om`, using the same receiver coins for all blocks; the round-`j` message is the tuple
`(y_j^{(i)})_{i ∈ [N/n]}`. `Open(state, I) = (m^{(i)}, Õpen(state^{(i)}))_{i ∈ B(I)}`, and
`Ver(ρ, τ, I, v, π)` parses `π = (u^{(i)}, π̃^{(i)})_{i ∈ B(I)}` with `u^{(i)} ∈ {0,1}^n` and accepts iff
the `(k − (i−1)n)`-th bit of `u^{(i)}`, `i = ⌈k/n⌉`, equals `v_k` for every `k ∈ I` (`v` indexed by the
positions of `I`), and `Ṽer(ρ, τ^{(i)}, u^{(i)}, π̃^{(i)}) = 1` for every `i ∈ B(I)`. -/
noncomputable def constr61 (C : Commit) (N : ℕ) : ICommit where
  N := N
  ℓ := C.ℓ
  R := C.R
  R_ne := C.R_ne
  σ := Str × (ℕ → C.σ)
  init := fun m => (m, fun i => C.init (block C.n m i))
  S := fun j st r =>
    (tupleEnc (N / C.n) ((List.range' 1 (N / C.n)).map fun i => (C.S j (st.2 i) r).1),
      (st.1, fun i => (C.S j (st.2 i) r).2))
  Open := fun st a b =>
    encList ((blocksOf C.n a b).flatMap fun i => [block C.n st.1 i, C.Open (st.2 i)])
  Ver := fun ρ τ a b v π =>
    let Bs := blocksOf C.n a b
    let L := (decList π).getD []
    let A₀ := (a + C.n - 1) / C.n
    decide ((decList π).isSome ∧ L.length = 2 * Bs.length ∧
      (∀ t < Bs.length, (L.getD (2 * t) []).length = C.n ∧
        C.Ver ρ (fun j => (tupleDec (N / C.n) (τ j)).getD (Bs.getD t 0 - 1) [])
          (L.getD (2 * t) []) (L.getD (2 * t + 1) []) = true) ∧
      ∀ k, a ≤ k → k ≤ b →
        (L.getD (2 * ((k + C.n - 1) / C.n - A₀)) []).getD (k - ((k + C.n - 1) / C.n - 1) * C.n - 1)
          false = v.getD (k - a) false)

/-- `J(I) = {(a' − 1)d̃ + 1, …, b'd̃}` where `B(I) = {a', …, b'}` (Theorem 6.2). -/
def blockJ (n d : ℕ) (a b : ℕ) : ℕ × ℕ :=
  (((a + n - 1) / n - 1) * d + 1, ((b + n - 1) / n) * d)

end SuccinctArgOWF.Kilian


