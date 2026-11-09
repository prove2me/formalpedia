-- Prove2me | Definitions.Def_PrivPCP_NestedCodes
-- name    : PrivPCP_NestedCodes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:03.062241+00:00
-- url     : https://prove2.me/theorems/63ab33cb-822b-4d13-b023-7dafebe7f134
-- title:
--   The nested codes of the general set-up of §4
-- statement:
--   Fix finite sets $S_i$ and linear codes $K_i,V_i\subseteq\mathbb F_q^{S_i}$; the standing assumption is $0\ne K_i\subsetneq V_i$. With duals for the standard dot product,
--   $$U_i=V_i^\perp,\quad W_i=K_i^\perp,\quad C=\bigotimes_i V_i,\quad E_i=K_i\otimes\bigotimes_{j\ne i}V_j,\quad K=\sum_i E_i,$$
--   $$B=C^\perp,\quad D_i=E_i^\perp,\quad D=\bigcap_i D_i=K^\perp.$$
--   For a coordinate subtuple $I$ the same spaces are formed from the restricted pairs $(K_i,V_i)_{i\in I}$ on $\prod_{i\in I}S_i$. A **mixed tuple** chooses $C_i\in\{U_i,W_i\}$ for each $i$. Finally
--   $$\delta_i=\frac{\min\{\mathrm{wt}(w): w\in W_i\setminus U_i\}}{s_i}.$$
--   These are the objects of Lemma 4.6, Corollary 4.10 and, through §4.1, Corollaries 4.3 and 4.4: $\mathrm{min}\{\mathrm{wt}(M):M\in D\setminus B\}$ is the privacy threshold of the randomized encoding.
--
--   **Formalization Note** The dual is the published `GoodQLTC.dualCode`.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §4 set-up, pp.12–13 (PDF pp.14–15); §4.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_PrivPCP_tensorCode

namespace PrivPCP

/-- The **nested codes of the general set-up of §4** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC
2027 submission manuscript (sha256 c2cac1e0…), §4 set-up, pp.12–13): finite coordinate sets `S_i`, `i ∈ ι`, and
for each `i` two linear codes `K_i, V_i ⊆ F^{S_i}`. The standing assumption `0 ≠ K_i ⊊ V_i` is `Valid`. -/
structure NestedCodes (F : Type) [Field F] (ι : Type) (S : ι → Type) where
  /-- the inner codes `K_i` -/
  K : ∀ i, Submodule F (S i → F)
  /-- the outer codes `V_i` -/
  V : ∀ i, Submodule F (S i → F)

namespace NestedCodes

variable {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
  (X : NestedCodes F ι S)

/-- The standing assumption `0 ≠ K_i ⊊ V_i` (p.13). -/
def Valid : Prop := ∀ i, X.K i ≠ ⊥ ∧ X.K i < X.V i

/-- `U_i = V_i^⊥` (dual for the standard dot product on `F^{S_i}`). -/
def U (i : ι) : Submodule F (S i → F) := GoodQLTC.dualCode (X.V i)

/-- `W_i = K_i^⊥`. -/
def W (i : ι) : Submodule F (S i → F) := GoodQLTC.dualCode (X.K i)

/-- `C = ⊗_i V_i`. -/
def C : Submodule F ((∀ i, S i) → F) := tensorCode X.V

/-- `E_i = K_i ⊗ ⊗_{j ≠ i} V_j`. -/
def E (i : ι) : Submodule F ((∀ i, S i) → F) := tensorCode (Function.update X.V i (X.K i))

/-- `K = ∑_i E_i`. -/
def Kbig : Submodule F ((∀ i, S i) → F) := ⨆ i, X.E i

/-- `B = C^⊥`. -/
def B : Submodule F ((∀ i, S i) → F) := GoodQLTC.dualCode X.C

/-- `D_i = E_i^⊥`. -/
def D (i : ι) : Submodule F ((∀ i, S i) → F) := GoodQLTC.dualCode (X.E i)

/-- `D = ⋂_i D_i = K^⊥`. -/
def Dbig : Submodule F ((∀ i, S i) → F) := GoodQLTC.dualCode X.Kbig

/-- The restricted pairs `(K_i, V_i)_{i ∈ I}` of a coordinate subtuple `I`, on `∏_{i∈I} S_i` (p.13: "For a
coordinate subtuple, we form the corresponding spaces from the restricted pairs"). -/
def restrict (I : Finset ι) : NestedCodes F {i // i ∈ I} (fun i => S i.val) :=
  ⟨fun i => X.K i.val, fun i => X.V i.val⟩

/-- The mixed tuple `(C_i)_i` with `C_i = U_i` where `b i` holds and `C_i = W_i` otherwise (§4.3, p.19). -/
def mixed (b : ι → Bool) (i : ι) : Submodule F (S i → F) := if b i then X.U i else X.W i

/-- `δ_i = min{wt(w) : w ∈ W_i ∖ U_i} / s_i` (§4.2, p.16). -/
noncomputable def relDualDist (i : ι) : ℝ :=
  (sInf {d | ∃ w ∈ X.W i, w ∉ X.U i ∧ GoodQLTC.supportCard w = d} : ℕ) / (Fintype.card (S i) : ℝ)

end NestedCodes

end PrivPCP


