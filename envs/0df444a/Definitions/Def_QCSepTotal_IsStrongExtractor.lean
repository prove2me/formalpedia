-- Prove2me | Definitions.Def_QCSepTotal_IsStrongExtractor
-- name    : QCSepTotal_IsStrongExtractor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:36:33.336852+00:00
-- url     : https://prove2.me/theorems/74dd6416-065a-4f1a-887c-4245fe9cb68f
-- title:
--   Strong $(k,\varepsilon)$-seeded extractor, eq. (3)
-- statement:
--   Let $b, c, d\ge1$ and let $E:\mathbb F_2^d\times\mathbb F_2^c\to\mathbb F_2^b$ be a map whose second argument is the seed; write $E_j(u)=E(u,j)$ for the fixed-seed maps. $E$ is a **strong $(k,\varepsilon)$-seeded extractor** if for every source $Z$ on $\mathbb F_2^d$ with min-entropy $H_\infty(Z)=-\log\max_z\Pr[Z=z]$ at least $k$, a seed $J$ drawn uniformly from $\mathbb F_2^c$ independently of $Z$ satisfies
--   $$\Delta\bigl((J, E_J(Z)),\ U_c\otimes U_b\bigr)\le\varepsilon ,$$
--   where $U_a$ is the uniform distribution on $\mathbb F_2^a$.
--
--   Lemma 2.3 provides such an extractor with linear surjective fixed-seed maps, and it compresses the lookup table in the construction of $F_{\mathrm{tot}}$.
--
--   **Formalization Note** $\mathbb F_2$ is the integers modulo $2$. The min-entropy is the published `SSNonExt.minEntropy` (binary logarithm). $U_c\otimes U_b$ is the uniform distribution on $\mathbb F_2^c\times\mathbb F_2^b$.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §2, p.4, eq. (3)

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QCSepTotal_tv

namespace QCSepTotal

/-- A **strong `(k, ε)`-seeded extractor** (F. Le Gall, *Improved Separations between Quantum and
Classical Communication Complexity of Total Functions*, arXiv:2609.16726, held version sha256
970e1476…, §2, p.4, eq. (3)): a map `E : F₂^d × F₂^c → F₂^m`, `(u, j) ↦ E(u, j)`, whose second
argument is the seed, such that for every source `Z` on `F₂^d` with min-entropy at least `k`,
a seed `J` uniform on `F₂^c` and independent of `Z` gives
`Δ((J, E_J(Z)), U_c ⊗ U_m) ≤ ε`.

**Formalization Note.** `F₂` is `ZMod 2`. The min-entropy is the published
`SSNonExt.minEntropy` (`−log₂ max_z Pr[Z = z]`). The joint law of `(J, E(Z, J))` is built from
the law of `Z` and an independent uniform seed; `U_c ⊗ U_m` is the uniform law on the product. -/
def IsStrongExtractor {d c m : ℕ}
    (E : (Fin d → ZMod 2) → (Fin c → ZMod 2) → (Fin m → ZMod 2)) (k ε : ℝ) : Prop :=
  ∀ Z : PMF (Fin d → ZMod 2), k ≤ SSNonExt.minEntropy Z →
    tv (Z.bind fun u => (PMF.uniformOfFintype (Fin c → ZMod 2)).map fun j => (j, E u j))
      (PMF.uniformOfFintype ((Fin c → ZMod 2) × (Fin m → ZMod 2))) ≤ ε

end QCSepTotal


