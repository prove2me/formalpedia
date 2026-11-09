-- Prove2me | Definitions.Def_InflMaxAdapt_Activates
-- name    : InflMaxAdapt_Activates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:12.720204+00:00
-- url     : https://prove2.me/theorems/ee77c1f9-a2a8-4130-9deb-38f5e97e182d
-- title:
--   Event "$v$ is probed by $\pi$ and activates $u$"
-- statement:
--   For live edges $E$, external randomness $\omega$ and vertices $v, u$, the seed $v$ is **probed by $\pi$ and activates $u$** if $\pi$ probes $v$, $u$ is connected to $v$, and $u$ is not connected to any seed probed by $\pi$ before $v$.
--
--   If $v$ is probed several times, only its first probe can activate $u$. For each realization at most one seed activates $u$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), proof of Lemma 4, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy_run
import Definitions.Def_InflMaxAdapt_Conn
import Definitions.Def_InflMaxAdapt_edgeCascade

namespace InflMaxAdapt

/-- "`v` is probed by `π` and activates `u`" (proof of Lemma 4, printed p.6 = PDF p.7, of
de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): `u` is connected to `v` but not to the seeds probed by `π` before `v`, for live edges `E` and
external randomness `ω`. Formally, some step `i` probes `v`, `u ↔ v`, and `u` is connected to none of
the seeds of steps `j < i`. If `v` is probed several times only its first probe can activate `u`. -/
def Activates {V : Type} [Fintype V] {k : ℕ} {Ω : Type} (E : Finset (Sym2 V)) (ω : Ω)
    (π : Policy V k Ω) (v u : V) : Prop :=
  ∃ i : Fin k, π.run ω (fun w => edgeCascade E {w}) i = v ∧ Conn E u v ∧
    ∀ j < i, ¬ Conn E u (π.run ω (fun w => edgeCascade E {w}) j)

end InflMaxAdapt


