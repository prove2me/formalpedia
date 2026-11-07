-- Prove2me | Definitions.Def_MetricMSO_IsCMSO1
-- name    : MetricMSO_IsCMSO1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:14.265746+00:00
-- url     : https://prove2.me/theorems/b6ce749a-0c97-4c44-bc55-9ea24f91921a
-- title:
--   The fragments $\mathrm{CMSO}_1[\mathsf{SP},\mathsf{EqGC}]$, $\mathrm{CMSO}_2$ and $\mathrm{MSO}_1$
-- statement:
--   Every formula is a $\mathrm{CMSO}_2[\mathsf{SP},\mathsf{EqGC}]$ formula. A formula is a $\mathrm{CMSO}_1[\mathsf{SP},\mathsf{EqGC}]$ formula if it uses no edge variable or edge-set variable, no incidence and no edge predicate. It is an ordinary $\mathrm{CMSO}_2$ formula if it has no $\mathsf{SP}$ and no $\mathsf{EqGC}$ atom. It is an ordinary $\mathrm{MSO}_1$ formula if it is in $\mathrm{CMSO}_1$, has no metric atom and has no modulo-counting atom.
--
--   **Formalization Note** The adjacency atom is kept in every fragment. In $\mathrm{MSO}_2$ it is expressible ("We can express adjacency by requiring two vertices to be distinct and to have an edge incident with both of them", p.16), so this changes no logic.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.7, p.16 (PDF 18); Definition 2.15, p.19 (PDF 21)

import Mathlib
import Definitions.Def_MetricMSO_Formula

namespace MetricMSO

namespace Formula

/-- `noMetric φ`: `φ` contains no SP and no EqGC atom, i.e. `φ` is an ordinary CMSO2 formula. -/
def noMetric : Formula → Bool
  | sp .. => false
  | eqgc .. => false
  | neg φ => noMetric φ
  | and φ ψ => noMetric φ && noMetric ψ
  | exV φ => noMetric φ
  | exE φ => noMetric φ
  | exVS φ => noMetric φ
  | exES φ => noMetric φ
  | _ => true

/-- `isCMSO1 φ`: `φ` uses no edge variable or edge-set variable, i.e. no `eqE`, `inc`, `memE`,
`epred`, `cardE`, `exE`, `exES`. Such a formula is a CMSO1[SP, EqGC] formula. -/
def isCMSO1 : Formula → Bool
  | eqE .. => false
  | inc .. => false
  | memE .. => false
  | epred .. => false
  | cardE .. => false
  | exE _ => false
  | exES _ => false
  | neg φ => isCMSO1 φ
  | and φ ψ => isCMSO1 φ && isCMSO1 ψ
  | exV φ => isCMSO1 φ
  | exVS φ => isCMSO1 φ
  | _ => true

/-- `noCard φ`: `φ` contains no modulo-counting atom. -/
def noCard : Formula → Bool
  | cardV .. => false
  | cardE .. => false
  | neg φ => noCard φ
  | and φ ψ => noCard φ && noCard ψ
  | exV φ => noCard φ
  | exE φ => noCard φ
  | exVS φ => noCard φ
  | exES φ => noCard φ
  | _ => true

end Formula

/-- **The fragments of CMSO2[SP, EqGC].**

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.7, p.16 (PDF 18), and
Definition 2.15, p.19 (PDF 21): "the guarded logics CMSO2[SP, EqGC] and CMSO1[SP, EqGC] extend CMSO2
and CMSO1, respectively, by SP and EqGC alone."

* every `Formula` is a CMSO2[SP, EqGC] formula;
* `IsCMSO1 φ`: `φ` is a CMSO1[SP, EqGC] formula (no edge or edge-set variables, no incidence, no
  edge predicates);
* `NoMetric φ`: `φ` is an ordinary CMSO2 formula (no SP, no EqGC atom); `IsCMSO1 φ ∧ NoMetric φ`
  is an ordinary CMSO1 formula;
* `IsMSO1 φ`: `φ` is an ordinary MSO1 formula (CMSO1, no metric atom, no modulo-counting atom).

**Formalization Note** The syntax keeps the adjacency atom `E(x, y)` in every fragment; in MSO2 it is
expressible ("We can express adjacency by requiring two vertices to be distinct and to have an edge
incident with both of them", p.16), so this changes no logic. -/
def IsCMSO1 (φ : Formula) : Prop := φ.isCMSO1 = true

/-- `φ` contains no SP and no EqGC atom (an ordinary CMSO2 formula). -/
def NoMetric (φ : Formula) : Prop := φ.noMetric = true

/-- `φ` is an ordinary MSO1 formula: CMSO1, no metric atom and no modulo-counting atom. -/
def IsMSO1 (φ : Formula) : Prop := φ.isCMSO1 = true ∧ φ.noMetric = true ∧ φ.noCard = true

end MetricMSO


