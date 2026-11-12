-- Prove2me | Definitions.Def_FourMsgQMA_Arg4_IsUniform
-- name    : FourMsgQMA_Arg4_IsUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:37:28.113869+00:00
-- url     : https://prove2.me/theorems/5cc1887c-0a24-436e-8c89-aa4bc2f98d5f
-- title:
--   Uniform polynomial-time algorithms of a four-message argument
-- statement:
--   An argument is **uniform** when every algorithm is polynomial-time computable:
--
--   1. the coin lengths, from $(1^\lambda,1^{|u|})$;
--   2. $\mathrm{Pre}$, $V_1$, $V_2$ and $\mathrm{Dec}$, from their packed inputs with $\lambda$ in unary;
--   3. the honest core, from $(1^\lambda,u,(y,a))$, and its two controllers, from $(1^\lambda,u,(y,a),1^j,\text{view})$;
--   4. the copy count $N(\lambda,t)$, from $(1^\lambda,1^t)$.
--
--   This pins down "PPT verifier", "deterministic classical algorithm" and "QPT prover" of §3.3. It also pins down "Policy and batch preprocessing … are charged as in the construction above" of Corollary 5.15: the construction's preprocessing cost $T_{\mathrm{setup}}+P(H)+(kN+s\log(k+s+2))\mathrm{poly}(\lambda)$ (p.38) is polynomial time.
--
--   **Formalization Note** Pinned-down version (operator request): polynomial time is `QAlgorithms.Complexity.PolyTimeComputable` (Mathlib's `TM2ComputableInPolyTime`).
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, p.11 (PDF 13); §5.1, p.38 (PDF 40); Corollary 5.15, p.44 (PDF 46)

import Mathlib
import Definitions.Def_FourMsgQMA_Arg4

namespace FourMsgQMA

open QAlgorithms.Complexity TightPQRepetition.Main

/-- Every algorithm of the argument is uniform and polynomial-time (§3.3, p.11: "A PPT verifier
preprocesses …", "a PPT verifier computes its next classical question", "A deterministic classical
algorithm outputs an acceptance bit", "a QPT prover"; Corollary 5.15, p.44: preprocessing "charged
as in the construction above", whose cost is polynomial, p.38).

1. The coin lengths are computed in polynomial time from `(1^λ, 1^{|u|})` (so they are polynomial
   in `λ + |u|`).
2. `Pre`, `V₁`, `V₂`, `Dec` are polynomial-time computable functions of their packed inputs
   (`λ` in unary, then the other inputs and the coins).
3. The honest prover is uniform: its core is computed in polynomial time from `(1^λ, u, w)`
   (`w` the classical witness), its two controllers in polynomial time from
   `(1^λ, u, w, 1^j, view)`, and the copy count `N(λ, t)` in polynomial time from `(1^λ, 1^t)`.

**Formalization Note** Pinned-down version (operator request): "PPT"/"QPT" are read as
`QAlgorithms.Complexity.PolyTimeComputable` (Mathlib's `TM2ComputableInPolyTime`) maps applied to
explicit uniform coins; the honest quantum core is over the finite gate set `H, S, T, X, CNOT`. -/
def Arg4.IsUniform (A : Arg4) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam m,
      g (pack [unary lam, unary m]) =
        pack [unary (A.coins0 lam m), unary (A.coins1 lam m), unary (A.coins2 lam m)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x r,
      g (pack [unary lam, x, r]) = A.pre lam x r) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam v r,
      g (pack [unary lam, v, r]) = pack [(A.v1 lam v r).1, (A.v1 lam v r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam v a r,
      g (pack [unary lam, v, a, r]) = pack [(A.v2 lam v a r).1, (A.v2 lam v a r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam v a,
      g (pack [unary lam, v, a]) = [A.dec lam v a]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x w,
      g (pack [unary lam, x, w]) = (A.core lam x w).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x w j v,
      g (pack [unary lam, x, w, unary j, v]) = A.toCore lam x w j v) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x w j v,
      g (pack [unary lam, x, w, unary j, v]) = A.toVerifier lam x w j v) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam t,
      g (pack [unary lam, unary t]) = unary (A.copies lam t))

end FourMsgQMA


