-- Prove2me | Definitions.Def_QPSpinProfile_marg
-- name    : QPSpinProfile_marg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:16.896342+00:00
-- url     : https://prove2.me/theorems/261cd232-e4be-417b-b930-ac067760c0c9
-- title:
--   Reduced state $\rho_T=\operatorname{Tr}_{S\setminus T}\rho$ and one-qubit marginals
-- statement:
--   For an operator $\rho$ on a finite set $S$ of qubits and $T\subseteq S$, the **reduced state** on $T$ is the partial trace over the other qubits,
--   $$
--   \rho_T(x,y)=\sum_{z\in\{0,1\}^{S\setminus T}}\rho\big((x,z),(y,z)\big),\qquad x,y\in\{0,1\}^T .
--   $$
--   A single site $i$ stands for $\{i\}$: $\rho_i=\operatorname{Tr}_{S\setminus\{i\}}\rho$ is a $2\times2$ matrix.
--
--   **Formalization Note** The subset $T$ is a decidable predicate on the site type, and $\rho_T$ is indexed by words on the subtype. The formula is the published partial trace $\operatorname{Tr}_B$ applied to the split $S=T\sqcup(S\setminus T)$, written directly because a subset of qubits is not a product factor of the index type.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §1.1, p.3 (PDF p.6)

import Mathlib

namespace QPSpinProfile

open Matrix

/-- The reduced state `ρ_T := Tr_{S∖T} ρ` on a subset `T` of the qubits `S` (arXiv:2610.02166,
held version sha256 a0a1ec89…, §1.1, p.3, PDF p.6): entries
`ρ_T(x, y) = ∑_{z ∈ {0,1}^{S∖T}} ρ((x, z), (y, z))`. Defined for any operator.

**Formalization Note** The subset is given by a decidable predicate `T` on the site type `S`;
the reduced operator is indexed by words on the subtype `{s // T s}`. -/
def marg {S : Type} [Fintype S] [DecidableEq S] (T : S → Prop) [DecidablePred T]
    (ρ : Matrix (S → Fin 2) (S → Fin 2) ℂ) : Matrix ({s // T s} → Fin 2) ({s // T s} → Fin 2) ℂ :=
  Matrix.of fun x y => ∑ z : ({s // ¬ T s} → Fin 2),
    ρ (fun s => if h : T s then x ⟨s, h⟩ else z ⟨s, h⟩)
      (fun s => if h : T s then y ⟨s, h⟩ else z ⟨s, h⟩)

/-- The one-qubit marginal `ρ_i := Tr_{S∖{i}} ρ` at a single site `i`, as a `2 × 2` matrix
(arXiv:2610.02166, §1.1, p.3, PDF p.6: "a single site `i` standing for `{i}`"). -/
def siteMarg {S : Type} [Fintype S] [DecidableEq S] (i : S)
    (ρ : Matrix (S → Fin 2) (S → Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (marg (fun s => s = i) ρ).submatrix (fun a _ => a) (fun a _ => a)

end QPSpinProfile


