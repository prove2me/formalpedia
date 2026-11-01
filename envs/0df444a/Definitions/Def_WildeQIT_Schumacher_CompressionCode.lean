-- Prove2me | Definitions.Def_WildeQIT_Schumacher_CompressionCode
-- name    : WildeQIT_Schumacher_CompressionCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:08.783241+00:00
-- url     : https://prove2.me/theorems/7d57e312-ea7a-4e86-995c-55dc312f35d7
-- title:
--   Quantum compression protocol of block length $n$
-- statement:
--   A quantum compression protocol of block length $n$ for a source on $\mathcal H_A = \mathbb C^a$ consists of
--
--   1. a compressed system $W$ of dimension $d = \dim\mathcal H_W$;
--   2. an encoding (compression) channel $\mathcal E_{A^n\to W}$;
--   3. a decoding (decompression) channel $\mathcal D_{W\to\hat A^n}$, where $\hat A^n$ is a copy of $A^n$.
--
--   Its rate and error are constrained by `IsCompressionCode`.
--
--   **Formalization Note** The channels are the published `WildeQIT.QChannel` (Choi–Kraus form, Theorem 4.4.1); $\mathcal H_{A^n}$ has standard basis indexed by sequences `Fin n → a`, and $\mathcal H_W$ by `Fin d`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §18.1, p. 523 and Figure 18.1

import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §18.1, p. 523: an
`(n, R, ε)` quantum compression code consists of an encoding (compression) channel
`E_{Aⁿ→W}`, where `W` is a quantum system of size `2^{nR}`, and a decoding (decompression)
channel `D_{W→Âⁿ}`.
-/

namespace WildeQIT.Schumacher

/-- **Quantum compression protocol of block length `n`** (Wilde, arXiv:1106.1445v8, §18.1,
p. 523, Figure 18.1). It consists of the dimension `d = dim(ℋ_W)` of the compressed system `W`,
an encoding channel `E_{Aⁿ→W}` and a decoding channel `D_{W→Âⁿ}`, where `ℋ_{Aⁿ}` has standard
basis indexed by `Fin n → a` and `Âⁿ` is a copy of `Aⁿ`.

**Formalization Note.** Channels are the published `WildeQIT.QChannel` (Choi–Kraus form, which by
Theorem 4.4.1 represents every CPTP map). The rate and error conditions are in
`IsCompressionCode`. -/
structure CompressionCode (a : Type) [Fintype a] [DecidableEq a] (n : ℕ) where
  /-- The dimension `dim(ℋ_W)` of the compressed system `W`. -/
  d : ℕ
  /-- The encoding (compression) channel `E_{Aⁿ→W}`. -/
  enc : WildeQIT.QChannel (Fin n → a) (Fin d)
  /-- The decoding (decompression) channel `D_{W→Âⁿ}`. -/
  dec : WildeQIT.QChannel (Fin d) (Fin n → a)

end WildeQIT.Schumacher


