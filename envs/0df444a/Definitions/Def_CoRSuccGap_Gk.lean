-- Prove2me | Definitions.Def_CoRSuccGap_Gk
-- name    : CoRSuccGap_Gk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:37.96587+00:00
-- url     : https://prove2.me/theorems/062036c6-ce36-49de-96f7-eb01513e2180
-- title:
--   The query $G_k(x,y)=\exists z\bigwedge_i[(P_i(x,y)\wedge Q_i(x,z))\vee(Q_i(x,y)\wedge P_i(x,z))]$ and the sentence $G_k^{\forall}$
-- statement:
--   Let $k\in\mathbb N$ and let the signature consist of the $2k$ binary relation symbols $P_1,\dots,P_k,Q_1,\dots,Q_k$. The single-quantifier positive three-variable formula
--
--   $$
--   G_k(x,y)\;:=\;\exists z\ \bigwedge_{i=1}^{k}\Big[\big(P_i(x,y)\wedge Q_i(x,z)\big)\vee\big(Q_i(x,y)\wedge P_i(x,z)\big)\Big]
--   $$
--
--   defines on each structure $\mathcal M$ with domain $D$ the binary query $[\![G_k]\!]^{\mathcal M}=\{(a,b)\in D^2:\mathcal M\models G_k[x\mapsto a,y\mapsto b]\}$. Note the crossed pairing: $P_i(x,y)$ goes with $Q_i(x,z)$ and $Q_i(x,y)$ with $P_i(x,z)$. The module also defines the truth value of the sentence
--
--   $$
--   G_k^{\forall}\;:=\;\forall x\,\forall y\,\big(x=y\vee G_k(x,y)\big).
--   $$
--
--   $G_k$ has size $O(k)$, yet Theorem 1.1 shows that every CoR circuit or term defining it needs $2^{k-1}$ compositions.
--
--   **Formalization Note** `GSym k` is the signature, with `GSym.P i`, `GSym.Q i` for $i\in$ `Fin k` standing for $P_{i+1},Q_{i+1}$. `Gk k M` is the query $[\![G_k]\!]^{\mathcal M}$, defined semantically (not through FO³ syntax), and `GkForall k M` is $\mathcal M\models G_k^{\forall}$.
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), §1.1, p.2 (PDF 4) for G_k; p.3 (PDF 5) for G_k^∀; binary queries §2.1, p.14 (PDF 16)

import Mathlib

set_option autoImplicit false

namespace CoRSuccGap

/-!
# The hard query G_k and the sentence G_k^∀

Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), §1.1, p.2 (PDF 4): "For k ≥ 1, we use the following single-quantifier positive FO³ formula
over 2k binary relation symbols P₁, …, P_k, Q₁, …, Q_k:
G_k(x, y) := ∃z ⋀_{i=1}^k [(P_i(x, y) ∧ Q_i(x, z)) ∨ (Q_i(x, y) ∧ P_i(x, z))]";
p.3 (PDF 5): "the FO³ sentence G_k^∀ := ∀x ∀y (x = y ∨ G_k(x, y))". Binary query of a formula:
§2.1, p.14 (PDF 16), ⟦φ⟧^M := {(a, b) ∈ D² : M ⊨ φ[x ↦ a, y ↦ b]}.

**Formalization Note.**
* `GSym k` is the signature {P₁, …, P_k, Q₁, …, Q_k}, indexed by `Fin k` (so P_{i+1} is `P i`).
* `Gk k M` is the binary query ⟦G_k⟧^M, defined semantically rather than through FO³ syntax;
  note the crossed pairing P_i(x,y) with Q_i(x,z) and Q_i(x,y) with P_i(x,z).
* `GkForall k M` is the truth value of the sentence G_k^∀ in `M`.
-/

/-- The signature of G_k: the 2k binary relation symbols P_i and Q_i, i ∈ Fin k. -/
inductive GSym (k : ℕ) where
  /-- The symbol P_{i+1}. -/
  | P (i : Fin k) : GSym k
  /-- The symbol Q_{i+1}. -/
  | Q (i : Fin k) : GSym k

/-- The binary query ⟦G_k⟧^M of
G_k(x, y) = ∃z ⋀_{i} [(P_i(x, y) ∧ Q_i(x, z)) ∨ (Q_i(x, y) ∧ P_i(x, z))] (p.2). -/
def Gk (k : ℕ) {D : Type*} (M : GSym k → D → D → Prop) : D → D → Prop :=
  fun x y => ∃ z, ∀ i : Fin k,
    (M (GSym.P i) x y ∧ M (GSym.Q i) x z) ∨ (M (GSym.Q i) x y ∧ M (GSym.P i) x z)

/-- The truth value in `M` of the sentence G_k^∀ = ∀x ∀y (x = y ∨ G_k(x, y)) (p.3). -/
def GkForall (k : ℕ) {D : Type*} (M : GSym k → D → D → Prop) : Prop :=
  ∀ x y, x = y ∨ Gk k M x y

end CoRSuccGap


