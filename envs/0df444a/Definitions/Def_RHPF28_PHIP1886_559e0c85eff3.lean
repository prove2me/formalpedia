-- Prove2me | Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
-- name    : RHPF28_PHIP1886_559e0c85eff3
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:00:03.121544+00:00
-- url     : https://prove2.me/theorems/734900d9-62ab-4cf4-a987-06bf0df8f847
-- title:
--   Definições auxiliares PHIP1886 — PF28
-- statement:
--   Para h,u,t inteiros, hat(h,u)=max(h−max(u,−u),0) é um chapéu triangular discreto e ramp(t,u)=max(t−u,0) é uma rampa. Os resultados de refinamento e diferença segunda serão publicados separadamente. Não há soma infinita, número primo ou afirmação sobre RH nessas definições.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL §166.1; código original PHIP1886. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e81ea9b87c905305c280d

import Mathlib
open MeasureTheory Set
noncomputable section
namespace PHIP1886

def hat (h u : Int) : Int := max (h - max u (-u)) 0

def ramp (t u : Int) : Int := max (t - u) 0

end PHIP1886


