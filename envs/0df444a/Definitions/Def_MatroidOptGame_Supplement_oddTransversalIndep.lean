-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_oddTransversalIndep
-- name    : MatroidOptGame_Supplement_oddTransversalIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:50:17.807122+00:00
-- url     : https://prove2.me/theorems/12b4c126-1b5e-46aa-a9e1-11c0fee23e37
-- title:
--   Independent sets of the matroid $\mathcal M_{n,H}$
-- statement:
--   Let $\mathcal M_{n,S_0,\pi}$ be the matroid with $S_0$ the even elements of $E_n$ and $\pi$ the pairing $\{2i,2i+1\}$, and let $H$ be an odd transversal with complement $\bar H=E_n\setminus H$. A set $S\subseteq E_n$ is **independent** in $\mathcal M_{n,H}$ if it is independent in $\mathcal M_{n,S_0,\pi}$, or $S=H$, or $S=\bar H$. Thus the bases of $\mathcal M_{n,H}$ are the $n$-sets containing a pair, the even transversals, and the two odd transversals $H$ and $\bar H$.
--
--   These are the hidden instances of the oracle lower bound on MIN's cost (Theorem 14): a MIN that cannot find $H$ cannot complete a cheap base.
--
--   **Formalization Note** Only the predicate; that it is a matroid is Lemma 12 of the paper.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, p.14

import Mathlib
import Definitions.Def_MatroidOptGame_Supplement_pairBaseIndep
import Definitions.Def_MatroidOptGame_Supplement_partner

namespace MatroidOptGame.Supplement

/-- Independence in the matroid `M_{n,H}` (Section 2.2.2): the matroid `M_{n,S₀,π}` with `S₀` the
even elements and `π` the pairing `{2i, 2i+1}`, with the odd transversal `H` and its complement
`H̄ = E_n ∖ H` added to the independent sets.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, p.14 ("Consider the matroid M_{n,S₀,π}, where S₀ consists of the
even-indexed elements of E_n, and π matches every pair 2i, 2i+1. … We now modify this matroid as
follows. Choose one odd transversal H, and let H̄ = E_n ∖ H … Add H and H̄ to the set of
independent sets. Denote the resulting set system by M_{n,H}").
**Formalization Note.** Only the predicate; that it is a matroid is Lemma 12 of the paper. It is
meant for `H` an odd transversal (`Supplement.OddTransversal`). -/
def oddTransversalIndep (n : ℕ) (H S : Finset (Fin (2 * n))) : Prop :=
  pairBaseIndep n (Finset.univ.filter (fun i : Fin (2 * n) => i.val % 2 = 0))
      (partner n) S ∨
    S = H ∨ S = Finset.univ \ H

end MatroidOptGame.Supplement


