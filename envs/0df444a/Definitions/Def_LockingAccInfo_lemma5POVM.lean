-- Prove2me | Definitions.Def_LockingAccInfo_lemma5POVM
-- name    : LockingAccInfo_lemma5POVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:04.135208+00:00
-- url     : https://prove2.me/theorems/d700030a-cc16-4d94-b9f2-54c1f299ee97
-- title:
--   The family $\mathcal N=\{\dim(E)\,P_V(v)\,\rho_{E|V=v}\}_v$ of Lemma 5
-- statement:
--   For a {cq}-state $\rho_{VE}$ the family
--
--   $$
--   \mathcal N:=\{\dim(E)\cdot P_V(v)\cdot\rho_{E|V=v}\}_{v\in V}
--   $$
--
--   of operators on $E$. It sums to $\dim(E)\,\rho_E$, so it is a POVM exactly when $\rho_E$ is the completely mixed state. Lemma 5 bounds the entropy of $V$ given any measurement outcome by the least outcome entropy of $\mathcal N$; in §III the same family, with $d=2^m$, is called $\mathcal N=\{d\cdot P_{XY}(x,y)\cdot\rho_{E|(X,Y)=(x,y)}\}$.
--
--   **Formalization Note** $\dim(E)$ is the cardinality of the finite index type of $E$.
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, Lemma 5, p.4; §III, p.2 (𝒩 in the proof of Lemma 2)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Lemma 5, p.4: for a {cq}-state ρVE,
"the POVM N := {dim(E) · PV(v) · ρE|V=v}v∈V" (and, in §III, p.2, the same construction
"N := {d · PXY(x, y) · ρE|(X,Y)=(x,y)}(x,y)∈X×Y where d := 2^m is the dimension of E").

**Formalization Note.** dim(E) is the cardinality of the finite index type `Q`. The family is a
POVM only when ρE is the completely mixed state; this is stated in the theorems (Lemma 5), not
built into the definition. -/
noncomputable def lemma5POVM {V Q : Type} [Fintype Q] (E : CQData V Q) (v : V) :
    Matrix Q Q ℂ :=
  (((Fintype.card Q : ℝ) * E.prob v : ℝ) : ℂ) • E.state v

end LockingAccInfo


