-- Prove2me | Definitions.Def_LockingAccInfo_withRegister
-- name    : LockingAccInfo_withRegister
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:23.316731+00:00
-- url     : https://prove2.me/theorems/eb292b74-95de-4e53-8101-f0aaf26a7e29
-- title:
--   Appending a classical register to $E$: the {cq}-state $\rho_{V(YE)}$ (footnote 23)
-- statement:
--   Let $\rho_{VE}=\sum_vP_V(v)|v\rangle\langle v|\otimes\rho_{E|V=v}$ be a {cq}-state and let $Y=\pi(V)$ be a classical value determined by $V$. Combining the systems $Y$ and $E$ gives the {cq}-state
--
--   $$
--   \rho_{V(YE)}=\sum_vP_V(v)\,|v\rangle\langle v|\otimes\bigl(|\pi(v)\rangle\langle\pi(v)|\otimes\rho_{E|V=v}\bigr),
--   $$
--
--   whose accessible information is $I_{\mathrm{acc}}(V;YE)$: the most information about $V$ a measurement on $Y$ and $E$ together can obtain.
--
--   **Formalization Note** The register is encoded in an orthonormal basis $\{|p\rangle\}$ and placed first: the combined system is the index type `P × Q`, built with a Kronecker product. The probabilities are those of $V$. In this mission $\pi$ is $(x,y)\mapsto y$ or the projection of the key onto its first $n-1$ bits.
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §II, p.2 (Δ) and footnote 23, p.5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §II, p.2 and footnote 23, p.5:
"Iacc(V; YE) denotes the accessible information of the {cq}-state ρV(YE) which is obtained from
ρVYE by combining the systems Y and E". Here the classical value Y = π(V) is a function of the
label V, and the combined system YE holds, given V = v, the state |π(v)⟩⟨π(v)| ⊗ ρE|V=v.

**Formalization Note.** The register Y is encoded in the orthonormal basis `{|p⟩}` of `ℂ^P`
(`Matrix.single p p 1` is `|p⟩⟨p|`), and the combined system is the index type `P × Q`, register
first, via the Kronecker product. The probabilities are unchanged. In this mission π is the
projection `(x, y) ↦ y` (the {ccq}-state of §III) or `(s', x) ↦ s'` (the first n − 1 key bits,
§VI (ii)). -/
noncomputable def withRegister {V P Q : Type} [DecidableEq P] (π : V → P) (E : CQData V Q) :
    CQData V (P × Q) where
  prob := E.prob
  state v := Matrix.kronecker (Matrix.single (π v) (π v) (1 : ℂ)) (E.state v)

end LockingAccInfo


