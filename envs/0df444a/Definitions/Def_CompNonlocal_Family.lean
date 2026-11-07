-- Prove2me | Definitions.Def_CompNonlocal_Family
-- name    : CompNonlocal_Family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:29.170553+00:00
-- url     : https://prove2.me/theorems/e0d323bf-0a02-49ec-b382-281827406790
-- title:
--   Circuit families indexed by the security parameter
-- statement:
--   A family assigns to each security parameter $\kappa\in\mathbb N$ a circuit with interface. Algorithms of the paper are such families ("the security parameter $1^\kappa$ is implicit in every algorithm's input"); a non-uniform family carries its classical advice in its circuits.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4, pp.17–18; §4.4, p.20

import Mathlib
import Definitions.Def_CompNonlocal_ICirc

set_option autoImplicit false

namespace CompNonlocal

/-- A circuit family indexed by the security parameter `κ`. Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), §4, pp.17–18: algorithms are run on "the security parameter κ" (§4.4, p.20: "The
security parameter 1^κ is implicit in every algorithm's input").

**Formalization Note** A non-uniform family carries its classical advice inside its circuits;
uniformity and size bounds are the separate predicates `Uniform` and `PolySize`. -/
abbrev Family := ℕ → ICirc

end CompNonlocal


