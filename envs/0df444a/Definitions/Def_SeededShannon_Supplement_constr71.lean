-- Prove2me | Definitions.Def_SeededShannon_Supplement_constr71
-- name    : SeededShannon_Supplement_constr71
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:40:18.753745+00:00
-- url     : https://prove2.me/theorems/1c3a2080-af3b-42a9-bd99-2371c8e3f225
-- title:
--   Construction 7.1 (list decoding and pruning)
-- statement:
--   Let $\Pi_{\mathrm{base}}$ be a seeded code for messages of length $k+v$ with codeword length $N$, and $H_K:\{0,1\}^k\to\{0,1\}^v$ a keyed hash, $K\leftarrow\mathrm{Gen}(1^\kappa,1^k,1^v)$.
--
--   1. $\mathrm{Setup}_u(1^\lambda,1^k)$: sample $K$ and, independently, $\sigma\leftarrow\Pi_{\mathrm{base}}.\mathrm{Setup}(1^\lambda,1^{k+v})$; output $\mathrm{crs}_u=(\sigma,K)$ with the length parameters.
--   2. $\mathrm{Encode}_u(\mathrm{crs}_u,x)=\Pi_{\mathrm{base}}.\mathrm{Encode}(\sigma,(x,H_K(x)))$.
--   3. $\mathrm{Decode}_u(\mathrm{crs}_u,y)$: compute $\mathcal L\leftarrow\Pi_{\mathrm{base}}.\mathrm{Decode}(\sigma,y)$, keep exactly the pairs $(x,z)\in\mathcal L$ with $z=H_K(x)$, and return $x$ if exactly one pair remains, otherwise $\bot$.
--
--   The codeword length and the supported lengths are those of the base code on $k+v$ bits. Theorem 7.10 shows that this pruning yields unique decoding.
--
--   **Formalization Note** $\kappa=\kappa(\lambda)$, $v=v(\lambda)$; $x$ is returned as the list $[x]$ and $\bot$ as the empty list; "exactly one pair remains" counts distinct pairs.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Construction 7.1, p.48 (PDF p.51)

import Mathlib
import Definitions.Def_SeededShannon_SeededCode
import Definitions.Def_SeededShannon_Supplement_parseTup
import Definitions.Def_SeededShannon_Supplement_CIHash

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- **Construction 7.1 (List decoding and pruning)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Construction 7.1, p.48), for a base seeded code
`Π_base` on messages of length `k + v` and the keyed hash `H_K = Hash(K, ·)` with
`K ← Gen(1^κ, 1^k, 1^v)`, `κ = κ(λ)`, `v = v(λ)`:
* `Setup_u(1^λ, 1^k)`: sample `K` and, independently, `σ ← Π_base.Setup(1^λ, 1^{k+v})`; output
  `crs_u = (σ, K)` with the length parameters;
* `Encode_u(crs_u, x) = Π_base.Encode(σ, (x, H_K(x)))`;
* `Decode_u(crs_u, y)`: `L ← Π_base.Decode(σ, y)`; keep exactly the pairs `(x, z) ∈ L` with
  `z = H_K(x)`; if exactly one pair remains, return its `x`, otherwise `⊥`.
The codeword length and the supported lengths are those of `Π_base` on `k + v` bits.

**Formalization Note** `crs_u = (1^λ, 1^k, K, σ)` in the tuple encoding; a message `(x, z)` is
`x ‖ z`; `x` is returned as the list `[x]` and `⊥` as `[]`. "Exactly one pair remains" counts
distinct pairs. Malformed inputs give the empty output. -/
noncomputable def constr71 (C : SeededCode) (H : CIHash) (κ v : ℕ → ℕ) : SeededCode where
  N := fun lam k => C.N lam (k + v lam)
  setupCoins := fun lam k => H.keyCoins (κ lam) k (v lam) + C.setupCoins lam (k + v lam)
  setup := fun lam k r =>
    QAdvFew.PoQOracle.tup [unary lam, unary k,
      H.gen (κ lam) k (v lam) (slice r 0 (H.keyCoins (κ lam) k (v lam))),
      C.setup lam (k + v lam) (slice r (H.keyCoins (κ lam) k (v lam)) (C.setupCoins lam (k + v lam)))]
  encode := fun crs x =>
    let lam := (tupGet crs 0).length
    let k := (tupGet crs 1).length
    if x.length = k then
      C.encode (tupGet crs 3)
        (x ++ bits (H.hash (κ lam) k (v lam) (tupGet crs 2) (fun i => x.getD i.val false)))
    else []
  decode := fun crs y =>
    let lam := (tupGet crs 0).length
    let k := (tupGet crs 1).length
    let S := (C.decode (tupGet crs 3) y).filter (fun u =>
      u.length = k + v lam ∧
        u.drop k = bits (H.hash (κ lam) k (v lam) (tupGet crs 2) (fun i => u.getD i.val false)))
    if S.dedup.length = 1 then S.dedup.map (fun u => u.take k) else []

end SeededShannon.Supplement


