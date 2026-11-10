-- Prove2me | Definitions.Def_PPSLattice_figOut
-- name    : PPSLattice_figOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:50.00732+00:00
-- url     : https://prove2.me/theorems/74e3cc12-cd25-4e25-a17e-b08ceed1df74
-- title:
--   The function computed by the circuit $C$ of Figure 1
-- statement:
--   With hardwired $\mathbf A\in\mathbb Z_q^{n\times\lceil\log N\rceil m}$, $\mathbf s\in\mathbb Z_q^n$, $\mathbf e\in\mathbb Z_q^{\lceil\log N\rceil m}$, $\mathbf P\in\mathbb Z_q^{n\times\lambda}$, $\tilde{\mathbf e},tg\in\mathbb Z_q^\lambda$, $i\in[N]$, $\mu\in\{0,1\}^\lambda$ and encoding randomness $r$, on input $b\in\{0,1\}^{nm\lceil\log q\rceil}$ parsed as $\mathbf B\in\mathbb Z_q^{n\times m}$:
--
--   1. $\mathbf c^\top=\mathbf s^\top(\mathbf A-\mathrm{encvec}(i)\otimes\mathbf G)+\mathbf e^\top$;
--   2. $\mathbf d^\top=\mathbf s^\top(\mathbf B\mathbf G^{-1}(\mathbf P))-\mathbf s^\top\mathbf P+\tilde{\mathbf e}^\top+tg$;
--   3. $h=\lceil tg\rfloor_2\oplus\mu$;
--
--   and the output is $(\mathbf c^\top,\mathbf P,\mathbf d^\top,h)$, each element $x\in\mathbb Z_q$ written as the $\ell_q$-bit binary code of $x+qr_j$, $\ell_q=\lceil\log q\rceil+\lambda$ (Remark 4.9), followed by the bits of $h$.
--
--   **Formalization Note** One fresh $r_j$ per output element of $\mathbb Z_q$: the proof of Lemma 4.22 needs independent encodings ("within statistical distance $k\cdot2^{-\lambda}$").
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Figure 1, p.22; Remark 4.9, p.22

import Mathlib
import Definitions.Def_PPSLattice_decMat
import Definitions.Def_AvoidPlast_fixedBits
import Definitions.Def_PPSLattice_encvec
import Definitions.Def_PPSLattice_kronG
import Definitions.Def_PPSLattice_gadgetInv
import Definitions.Def_PPSLattice_round2
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **function computed by the circuit `C` of Figure 1**, with the encoding of Remark 4.9. Hardwired:
`A ∈ Z_q^{n×(⌈log N⌉·m)}`, `s ∈ Z_q^n`, `e ∈ Z_q^{⌈log N⌉·m}`, `P ∈ Z_q^{n×λ}`, `ẽ, tg ∈ Z_q^λ`, the index `i`, the
message `µ`, and the encoding randomness `r = (r_0, r_1, …)`. On input `b ∈ {0,1}^{n·m·⌈log q⌉}`, parsed as
`B ∈ Z_q^{n×m}` (row-major, `⌈log q⌉` bits per entry):
1. `c^⊤ = s^⊤(A − encvec(i) ⊗ G) + e^⊤`;
2. `d^⊤ = s^⊤(B G^{-1}(P)) − s^⊤P + ẽ^⊤ + tg`;
3. `h = ⌈tg⌋₂ ⊕ µ`;
and the output is `(c^⊤, P, d^⊤, h)`: the `⌈log N⌉·m + nλ + λ` elements of `Z_q` in this order (`P` row-major),
the `j`-th written as the `ℓ_q`-bit binary code of `x + q·r_j` with `ℓ_q = ⌈log q⌉ + λ`, followed by the `λ`
bits of `h`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Figure 1, p.22; Remark 4.9, p.22 ("C (Figure 1) outputs each x ∈ Z_q as the ℓ_q-bit binary
representation of x + qr where ℓ_q := ⌈log q⌉ + λ and r ← [0, ⌊2^{ℓ_q}/q⌋ − 1] is sampled by skEnc and
hardwired in C").

**Formalization Note.** Remark 4.9 is read with one fresh `r_j` per output element of `Z_q`: the proof of
Lemma 4.22 (p.29) needs the encodings of the `k` uniform elements to be independent ("within statistical
distance k · 2^{−λ}"). Binary codes are least significant bit first; `x` is the representative in `[0, q)`. -/
def figOut (q n m N lam : ℕ) (A : Matrix (Fin n) (Fin (Nat.clog 2 N * m)) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin (Nat.clog 2 N * m) → ZMod q)
    (P : Matrix (Fin n) (Fin lam) (ZMod q)) (et tg : Fin lam → ZMod q) (i : ℕ) (mu : Str)
    (r : List ℕ) (b : Str) : Str :=
  let Bm : Matrix (Fin n) (Fin m) (ZMod q) := decMat q n m b
  let c : Fin (Nat.clog 2 N * m) → ZMod q := fun j =>
    (∑ t, s t * (A - kronG q n m (Nat.clog 2 N) (encvec N i)) t j) + e j
  let d : Fin lam → ZMod q := fun j =>
    (∑ t, s t * (Bm * gadgetInv q n m P) t j) - (∑ t, s t * P t j) + et j + tg j
  let h : Str := List.ofFn fun j : Fin lam => xor (round2 (tg j)) (mu.getD j false)
  let elems : List (ZMod q) := List.ofFn c ++
    List.ofFn (fun t : Fin (n * lam) => P (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) ++
    List.ofFn d
  (elems.mapIdx fun j x => AvoidPlast.fixedBits (Nat.clog 2 q + lam) (x.val + q * r.getD j 0)).flatten ++ h

end PPSLattice


