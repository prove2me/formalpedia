-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Terminals
-- name    : LeeCutCertificates_Certificate_Terminals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:04.149339+00:00
-- url     : https://prove2.me/theorems/6494b9be-cc4f-4e05-92b5-9de5aca8553a
-- title:
--   Terminal cuts, isolating values and their certificates
-- statement:
--   Let $A,B\subseteq V$ be disjoint nonempty terminal sets. An $A$–$B$ shore contains $A$ and avoids $B$. Its optimum value is
--
--   $$\nu_G(A,B)=\min_{A\subseteq S,\ S\cap B=\varnothing}c_G(S).$$
--
--   For $v\in R$ and $|R|\ge2$, the isolating value is
--
--   $$\operatorname{iso}_G(v;R)=\nu_G(\{v\},R\setminus\{v\})=\min_{S\cap R=\{v\}}c_G(S).$$
--
--   A terminal-value certificate preserves $\nu_G(A,B)$ in all consistent nonnegative competitors. A terminal-witness certificate additionally queries an optimum shore and preserves its optimality. An isolating certificate preserves every value $\operatorname{iso}_G(v;R)$, $v\in R$, simultaneously using one family of queries. A shore separates $U$ if it meets $U$ and misses at least one terminal of $U$. These notions supply the terminal interfaces of Lemmas 2 and 11–13.
--
--   **Formalization Note** The real infimum is over a finite nonempty family whenever the terminal assumptions used in the theorems hold, so it is an attained minimum. On an empty eligible family (intersecting $A,B$), the total real infimum is zero; no theorem uses that case. With $v\in R$ and $|R|\ge2$, both isolating terminal sets are nonempty. Terminal nonemptiness is imposed in the theorem binders, rather than assumed inside the graph model. Empty and singleton $U$ remain allowed in the splitting-off statement.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §7.1, printed pp.19–21 (PDF pp.20–22); §7.2, printed p.21 (PDF p.22); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_CutQueries

set_option autoImplicit false
open SunMinCut.Cactus
open Classical

namespace LeeCutCertificates.Certificate

/-- An A–B separating shore, oriented toward A. -/
def TerminalShore {n : ℕ} (A B S : Finset (Fin n)) : Prop := A ⊆ S ∧ Disjoint S B

/-- Minimum over a finite nonempty family when A,B are disjoint and nonempty.
On an empty family the real sInf convention is zero; no theorem uses that case. -/
noncomputable def terminalValue {n m : ℕ} (G : Graph n m) (A B : Finset (Fin n)) : ℝ :=
  sInf {x : ℝ | ∃ S : Finset (Fin n), TerminalShore A B S ∧ x = cutw G S}

/-- Minimum cut isolating v from the other vertices of R; used for v ∈ R, |R| ≥ 2. -/
noncomputable def iso {n m : ℕ} (G : Graph n m) (v : Fin n) (R : Finset (Fin n)) : ℝ :=
  terminalValue G {v} (R \ {v})

/-- Simultaneous certification of all terminal isolating values by one fixed family. -/
def IsolatingCertificate {n m : ℕ} (G : Graph n m) (R : Finset (Fin n))
    (Q : Finset (Finset (Fin n))) : Prop :=
  ∀ (k : ℕ) (H : Graph n k), Nonnegative H → Agrees G H Q →
    ∀ v ∈ R, iso H v R = iso G v R

/-- Certificate for a terminal separating-cut value. -/
def TerminalValueCertificate {n m : ℕ} (G : Graph n m) (A B : Finset (Fin n))
    (Q : Finset (Finset (Fin n))) : Prop :=
  ∀ (k : ℕ) (H : Graph n k), Nonnegative H → Agrees G H Q →
    terminalValue H A B = terminalValue G A B

/-- The value and the queried optimum shore both persist. -/
def TerminalWitnessCertificate {n m : ℕ} (G : Graph n m) (A B : Finset (Fin n))
    (Q : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  TerminalValueCertificate G A B Q ∧ S ∈ Q ∧ TerminalShore A B S ∧
    cutw G S = terminalValue G A B ∧
    ∀ (k : ℕ) (H : Graph n k), Nonnegative H → Agrees G H Q →
      cutw H S = terminalValue H A B

/-- A shore contains a terminal on each side. -/
def Separates {n : ℕ} (U S : Finset (Fin n)) : Prop :=
  (S ∩ U).Nonempty ∧ ¬ U ⊆ S

end LeeCutCertificates.Certificate


