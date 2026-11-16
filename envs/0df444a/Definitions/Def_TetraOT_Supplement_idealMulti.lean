-- Prove2me | Definitions.Def_TetraOT_Supplement_idealMulti
-- name    : TetraOT_Supplement_idealMulti
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:41:02.857554+00:00
-- url     : https://prove2.me/theorems/2a7ef198-9299-4344-b4d3-dcfb8a15aa3e
-- title:
--   The ideal functionality ½ROT$_g$ of the Multi Tetrahedral Protocol
-- statement:
--   The ideal functionality of Theorems 10.1 and 10.2, for parameters $m, n_A, n_B$:
--
--   1. draw the role map $R$ (which ranks are good, and who sends at each) from its law in the real protocol, i.e. as the role map of a uniform $\rho\in S_{4m}$;
--   2. independently, draw independent uniform bits $(m_0^r, m_1^r, s^r)$ for every rank $r$;
--   3. give $R$ to both parties; at a rank where Alice sends, Alice gets $(m_0^r,m_1^r)$ and Bob gets $(s^r, m^r_{s^r})$; at a rank where Bob sends, the roles are swapped; off the good set both get nothing.
--
--   So, given the role map, the parties hold $g$ independent random 1-of-2 oblivious transfers, oriented by role, with $g$ distributed as $g(\rho)$ (Fig. 31: "½ROT$_g$"; §10.3: "the distribution for any successful $r$ is uniform regardless of the failed $r'$ cases").
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Fig. 31 and §10.3, p.12 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Supplement_multiRun

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- **The ideal functionality ½ROT_g of the Multi Tetrahedral Protocol** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 31 and §10.3,
p.12; p. = PDF page, the PDF has no printed page numbers): "The Multi Tetrahedral Protocol for ½ROT_g";
"the distribution for any successful r is uniform regardless of the failed r′ cases".

1. The role map `R : Fin m → Option Bool` is drawn from its law in the real protocol (the image of the
   uniform deal `ρ ∈ S_n` under `roleMap`); `R r = some true` means Alice is the sender at rank `r`,
   `some false` that Bob is, `none` that `r ∉ G`.
2. Independently, `x : Fin m → Bool × Bool × Bool` is drawn uniformly: independent uniform bits
   `(m₀, m₁, s)` for every rank.
3. Both parties receive `R`. At a rank with `R r = some true`, Alice receives `(m₀, m₁)` and Bob
   `(s, m_s)`; with `R r = some false`, Bob receives `(m₀, m₁)` and Alice `(s, m_s)`; with `R r = none`
   both receive `none`.

So, given `R`, the parties hold `g = |{r : R r ≠ none}|` independent instances of the random 1-of-2
oblivious transfer (each with the law `TetraOT.idealROT` of Definition 2.5), oriented by role.

**Formalization Note.** `m_s = m₁` if `s = true`, `m₀` otherwise; bits are `Bool` with `true` = 1. The
output types match `multiAliceOut` and `multiBobOut`. -/
noncomputable def idealMulti (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) :
    PMF (((Fin m → Option Bool) × (Fin m → Option (Bool × Bool))) ×
      ((Fin m → Option Bool) × (Fin m → Option (Bool × Bool)))) :=
  ((multiDeal m).map (roleMap m nA nB h)).bind (fun R =>
    (PMF.uniformOfFintype (Fin m → Bool × Bool × Bool)).map (fun x =>
      ((R, fun r => (R r).map (fun b =>
          if b then ((x r).1, (x r).2.1)
          else ((x r).2.2, if (x r).2.2 then (x r).2.1 else (x r).1))),
       (R, fun r => (R r).map (fun b =>
          if b then ((x r).2.2, if (x r).2.2 then (x r).2.1 else (x r).1)
          else ((x r).1, (x r).2.1))))))

end TetraOT.Supplement


