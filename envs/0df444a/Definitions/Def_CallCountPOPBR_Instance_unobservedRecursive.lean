-- Prove2me | Definitions.Def_CallCountPOPBR_Instance_unobservedRecursive
-- name    : CallCountPOPBR_Instance_unobservedRecursive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:15.741196+00:00
-- url     : https://prove2.me/theorems/8306aac9-5b15-4543-bf50-71d8446030ed
-- title:
--   Number of unobserved recursive indices
-- statement:
--   For an instance $(N,d,p,\mathrm{Obs})$, the number of **unobserved recursive indices** is
--   $$
--   U=\#\{\,n : d\le n\le N,\ \mathrm{Obs}(n)\text{ undefined}\,\}.
--   $$
--
--   Theorem 2.8 states that NP-hardness holds for instances with few such indices.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Theorem 2.8, p.6

import Definitions.Def_CallCountPOPBR_Instance

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Number of unobserved recursive indices.** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Theorem 2.8, p.6: "NP-hardness holds
already for instances with p = N + 1, d = (N + 1)/2, and only K ≤ n − 1 unobserved recursive
indices."

The number of indices `n` with `d ≤ n ≤ N` that carry no observation. -/
def Instance.unobservedRecursive (I : Instance) : ℕ :=
  ((Finset.Icc I.d I.N).filter (fun n => I.obs.getD n none = none)).card

end CallCountPOPBR


