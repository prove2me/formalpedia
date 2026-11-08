-- Prove2me | Definitions.Def_WICanon_TranscriptFamily
-- name    : WICanon_TranscriptFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:19.063089+00:00
-- url     : https://prove2.me/theorems/b2502b5e-09a1-41d3-838e-81da85e69e6d
-- title:
--   The prefix family and the transcript family $f_a(i,b,r_P,r_V)$
-- statement:
--   For a family $f_a$ the **prefix family** is $f'_a(i,x)=f_a(x)_{\le i}$. For a protocol $(P,V)$ for $\mathcal R$ the **transcript family** is, for $a=(x,w_0,w_1)$ with $(x,w_0),(x,w_1)\in\mathcal R$, a bit $b$, an index $i$ and coins $r_P,r_V$,
--
--   $$f_a(i,b,r_P,r_V)=\langle P(x,w_b;r_P),V(x;r_V)\rangle_{\le i}.$$
--
--   It says: on input the index, the bit and both coin tapes, output the first $i$ bits of the transcript of the execution on $(x,w_b)$. This family is the candidate one-way function of the paper.
--
--   **Formalization Note** The index $i\in[L]$ is read from $\lceil\log_2 L\rceil$ uniform bits, as $\min(\mathrm{val}(s)+1,L)$, so every value has probability at least $1/(2L)$. The index $a$ is written with the published injective code `tup`, padded by empty components to a fixed length. Strings of another form are not indices, as a garbage index could be hard for reasons unrelated to the protocol. Equal witnesses are allowed; the proof of Theorem 3.1 uses $a=(x,w,w)$.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem 3.1, p.16; Lemma 3.10, p.22; Theorem 3.7, p.21

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_Protocol

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ

/-- The rank of `s` among the strings of its length in lexicographic order: `s` read as a binary
number, most significant bit first. -/
def lexRank (s : Str) : ℕ := s.foldl (fun acc b => 2 * acc + b.toNat) 0

/-- The index `i ∈ [L]` encoded by the bit string `s`.

**Formalization Note.** Printed, `i` is uniform in `[ℓ]`, which is not a uniform bit string. Here
`i = min(val(s) + 1, L)` for `s` of `⌈log₂ L⌉` bits, so each value has probability at least `1/(2L)`. -/
def bitsToIndex (L : ℕ) (s : Str) : ℕ := min (lexRank s + 1) L

/-- The domain length of the prefix family: `⌈log₂ L(n)⌉` index bits and `m(n)` input bits. -/
def prefixDomain (L m : ℕ → ℕ) (n : ℕ) : ℕ := Nat.clog 2 (L n) + m n

/-- The family `f'_a(i, x) := f_a(x)_{≤i}` of Theorem 3.7, p.21, with `i ∈ [L(n)]` encoded in the
leading bits of the input. -/
def prefixFamily (L : ℕ → ℕ) (f : ℕ → Str → Str → Str) (n : ℕ) (a y : Str) : Str :=
  (f n a (y.drop (Nat.clog 2 (L n)))).take (bitsToIndex (L n) (y.take (Nat.clog 2 (L n))))

/-- The index `a = (x, w_0, w_1)` as a string of fixed length `2n + 4q(n) + 6` (when
`|w_0|, |w_1| ≤ q(n)`). The padding is by empty components of `tup`, so `tup` still parses it. -/
def encodeInstance (q : Polynomial ℕ) (x w₀ w₁ : Str) : Str :=
  tup (x :: w₀ :: w₁ ::
    List.replicate (2 * q.eval x.length - w₀.length - w₁.length) [])

/-- The valid indices of the family of Theorem 3.1 and Lemma 3.10: `a = (x, w_0, w_1)` with `|x| = n`,
`(x, w_0) ∈ R_n` and `(x, w_1) ∈ R_n`. Equal witnesses are allowed (the proof of Theorem 3.1 uses
`a = (x, w, w)`, p.23). Other strings are not indices: garbage indices could be hard for reasons
unrelated to the protocol, which would weaken alternative 1 of Theorem 3.1. -/
def transcriptValid (R : Relation) (q : Polynomial ℕ) (n : ℕ) (a : Str) : Prop :=
  ∃ x w₀ w₁, x.length = n ∧ R x w₀ ∧ R x w₁ ∧ a = encodeInstance q x w₀ w₁

/-- The encoded full transcript on index `a = (x, w_0, w_1)` and input `y = (b, r_P, r_V)`. -/
noncomputable def transcriptFull (pv : Protocol) (n : ℕ) (a y : Str) : Str :=
  match untuple a with
  | some (x :: w₀ :: w₁ :: _) =>
    let b := y.headD false
    let rest := y.drop 1
    tup (pv.transcript x (if b then w₁ else w₀)
      (rest.take (pv.coinsP n)) (rest.drop (pv.coinsP n)))
  | _ => []

/-- `m(n)` of `transcriptFull`: one bit `b`, then the two coin tapes. -/
def transcriptInputLen (pv : Protocol) (n : ℕ) : ℕ := 1 + pv.coinsP n + pv.coinsV n

/-- **The transcript family** of Theorem 3.1, p.16 and Lemma 3.10, p.22:
`f_a(i, b, r_P, r_V) := ⟨P(x, w_b; r_P), V(x; r_V)⟩_{≤i}`, with `i ∈ [L(n)]`.

**Formalization Note.** `≤i` means the first `i` bits of the transcript ("the first i bits of the
transcript", p.17); the transcript is written with the injective code `tup`, and `L` bounds that
encoded length. -/
noncomputable def transcriptFamily (pv : Protocol) (L : ℕ → ℕ) : ℕ → Str → Str → Str :=
  prefixFamily L (transcriptFull pv)

/-- The domain length of `transcriptFamily`. -/
def transcriptDomain (pv : Protocol) (L : ℕ → ℕ) : ℕ → ℕ :=
  prefixDomain L (transcriptInputLen pv)

end WICanon


