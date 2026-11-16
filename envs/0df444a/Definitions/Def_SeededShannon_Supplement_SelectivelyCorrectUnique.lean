-- Prove2me | Definitions.Def_SeededShannon_Supplement_SelectivelyCorrectUnique
-- name    : SeededShannon_Supplement_SelectivelyCorrectUnique
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:35:53.65329+00:00
-- url     : https://prove2.me/theorems/53eefe60-9e8d-4a3e-952a-9ce468e1fe23
-- title:
--   Selective $p$-correction with unique decoding (Definition 3.15)
-- statement:
--   Let $\Pi=(\mathrm{Setup},\mathrm{Encode},\mathrm{Decode})$ be a seeded code whose decoder outputs a single message or $\bot$, identified with a list of size at most one. In the selective error-correction experiment $\mathrm{ExpCorrect}^{(p)}(\mathcal A,\lambda)$, the adversary $\mathcal A_1$ sends a message $x^*\in\{0,1\}^k$ of a supported length, the challenger samples $\mathrm{crs}\leftarrow\mathrm{Setup}(1^\lambda,1^k)$, and $\mathcal A_2(\mathrm{st},\mathrm{crs})$ sends $y\in\{0,1\}^N$. The experiment outputs $1$ if
--   $$\Delta(\mathrm{Encode}_{\mathrm{crs}}(x^*),y)\le p\cdot N\quad\wedge\quad \mathrm{Decode}_{\mathrm{crs}}(y)\ne x^*.$$
--   $\Pi$ **selectively $p$-corrects with unique decoding** if for every polynomial-size adversary there is a negligible $\nu$ with $\Pr[\mathrm{ExpCorrect}^{(p)}(\mathcal A,\lambda)=1]\le\nu(\lambda)$ for all $\lambda$.
--
--   This is the unique-decoding guarantee of Theorems 7.10 and 7.15.
--
--   **Formalization Note** It mirrors the published `SeededShannon.SeededCode.SelectivelyCorrect` exactly (nonuniform deterministic adversaries, the first stage a fixed message sequence, malformed outputs count as $0$), changing only the failure condition to $\mathrm{Decode}_{\mathrm{crs}}(y)\ne[x^*]$. Unique decodability itself is the published list bound with $L=1$.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 3.15, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_SeededShannon_SeededCode

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- **Selective `p`-correction with unique decoding** (Dujmovic, Lu, Silbak, Wichs, *Shannon Rate
Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript sha256
52f4b606…a769709), Definition 3.15, p.22: "A uniquely decodable code instead outputs a single
message or `⊥`, which we identify with a list of size at most one. … For a uniquely decodable code,
`L = 1` and the failure condition reads `Decode_crs(y) ≠ x*`; we then say that `Π` selectively
`p`-corrects with unique decoding"): the experiment `ExpCorrect^{(p)}` of the published
`SeededCode.SelectivelyCorrect`, with the failure condition `x* ∉ Decode_crs(y)` replaced by
`Decode_crs(y) ≠ x*`.

**Formalization Note** The decoder's output `x` is the one-element list `[x]` and `⊥` is the empty
list, so `Decode_crs(y) ≠ x*` is `decode crs y ≠ [x*]`. Adversaries, the hard-wired first stage, the
treatment of malformed outputs and the order of quantifiers are exactly those of the published
`SeededCode.SelectivelyCorrect`. Unique decodability itself (lists of size at most one) is the
published `SeededCode.ListBound` with `L = 1`. -/
def SelectivelyCorrectUnique (C : SeededCode) (supp : ℕ → ℕ → Prop) (p : ℝ) : Prop :=
  ∀ xs : ℕ → List Bool, PolyBounded (fun lam => (xs lam).length) →
  ∀ A : CircFamily, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, supp lam (xs lam).length →
    wprob (unifW (Fin (C.setupCoins lam (xs lam).length) → Bool)) (fun r =>
      let crs := C.setup lam (xs lam).length r
      let y := (A.circ lam).eval (padIn (A.inLen lam) (QAdvFew.PoQOracle.tup [unary lam, crs]))
      y.length = C.N lam (xs lam).length ∧
        (ldist (C.encode crs (xs lam)) y : ℝ) ≤ p * C.N lam (xs lam).length ∧
        C.decode crs y ≠ [xs lam]) ≤ ν lam

end SeededShannon.Supplement


