-- Prove2me | Definitions.Def_KarpLiptonOM_toPromise
-- name    : KarpLiptonOM_toPromise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:59.723029+00:00
-- url     : https://prove2.me/theorems/8ff5c865-ecbf-4675-9db5-52873cd48e39
-- title:
--   A language $L$ as the promise problem $(L, \overline L)$
-- statement:
--   A language $L \subseteq \{0,1\}^*$ is identified with the promise problem $(L, \overline L)$, whose promise is satisfied by every string. The only language consistent with $(L, \overline L)$ is $L$ itself, so for a language oracle the class $\mathrm P^L$ is the usual one.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem

namespace KarpLiptonOM

/-- A language `L` identified with the promise problem `(L, L̄)` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21: "a language
`L` is identified with `(L, L̄)`"). -/
def toPromise (L : Set (List Bool)) : PromiseProblem := ⟨L, Lᶜ, disjoint_compl_right⟩

end KarpLiptonOM


