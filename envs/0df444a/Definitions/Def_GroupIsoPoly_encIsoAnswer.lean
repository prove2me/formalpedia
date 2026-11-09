-- Prove2me | Definitions.Def_GroupIsoPoly_encIsoAnswer
-- name    : GroupIsoPoly_encIsoAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:24.795667+00:00
-- url     : https://prove2.me/theorems/0e229249-b6fe-4c20-89d1-973cd95519df
-- title:
--   Binary code of an isomorphism-coset answer for labelled groups
-- statement:
--   Let $G,H$ be groups of order $N$ with labellings $e_G,e_H$. An isomorphism $\varphi:G\to H$ is written as its table of labels $\big(e_H(\varphi(e_G^{-1}(i)))\big)_{i<N}$ and an automorphism $\sigma$ of $G$ as $\big(e_G(\sigma(e_G^{-1}(i)))\big)_{i<N}$. An answer — emptiness, or an isomorphism $\varphi$ with a list of automorphisms of $G$ — is coded by the coset-answer code applied to these label tables.
--
--   A correct answer of this kind describes the whole coset $\mathrm{Iso}(G,H)=\varphi\cdot\mathrm{Aut}(G)$.
--
--   **Formalization Note** The labels are those of the input tables, so the output is meaningful to an algorithm that sees only the tables.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 9.1, p.92 (PDF p.96); §9.6, p.119 (PDF p.123)

import Mathlib
import Definitions.Def_GroupIsoPoly_encAnswer

set_option autoImplicit false

namespace GroupIsoPoly

/-- An isomorphism `φ : G ≃* H` between labelled groups, written as the list of the `N` labels
`eH (φ (eG⁻¹ i))`. -/
def isoLabels {G H : Type*} [Group G] [Group H] {N : ℕ} (eG : G ≃ Fin N) (eH : H ≃ Fin N)
    (φ : G ≃* H) : List ℕ :=
  List.ofFn fun i : Fin N => (eH (φ (eG.symm i)) : ℕ)

/-- An automorphism `σ` of a labelled group, written as the list of the `N` labels `eG (σ (eG⁻¹ i))`. -/
def autLabels {G : Type*} [Group G] {N : ℕ} (eG : G ≃ Fin N) (σ : MulAut G) : List ℕ :=
  List.ofFn fun i : Fin N => (eG (σ (eG.symm i)) : ℕ)

/-- **The binary code of an isomorphism-coset answer for labelled groups.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 9.1, p.92 (PDF p.96): "computes the coset
Iso(G, H)"; §9.6, p.119 (PDF p.123): "These lifts and kernel generators generate Aut(G)".

An answer is emptiness, or an isomorphism `φ : G ≃* H` with a list of automorphisms of `G`. It is
written with `encAnswer`, each map given by its table of labels.

**Formalization Note.** The labels are those of the input tables, so the output is meaningful to the
machine, which sees only the tables. -/
def encIsoAnswer {G H : Type*} [Group G] [Group H] {N : ℕ} (eG : G ≃ Fin N) (eH : H ≃ Fin N)
    (ans : Option ((G ≃* H) × List (MulAut G))) : List Bool :=
  encAnswer (ans.map fun a => (isoLabels eG eH a.1, a.2.map (autLabels eG)))

end GroupIsoPoly


