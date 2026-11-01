-- Prove2me | Definitions.Def_BudgetCoreExchange_gadget
-- name    : BudgetCoreExchange_gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:29.410389+00:00
-- url     : https://prove2.me/theorems/01fd7370-9878-42ce-96ef-13493570c027
-- title:
--   The exchange CEx$_\varphi$ of the reduction from QSAT$_2$ and $nW$-equilibria
-- statement:
--   Fix a DNF formula $\varphi(x,y)$ with $n$ $x$-variables, $m$ $y$-variables and terms $C_1,\dots,C_L$, and constants $T,U,V,W$. The exchange $\mathrm{CEx}_\varphi$ has the following items, sellers and buyers.
--
--   **Sellers and items** (each seller values everything at $0$):
--
--   1. $S^\chi_i$ ($i\le n$) owns $\chi_i,\bar\chi_i$;
--   2. $S^\psi_l$ ($l\le L$) owns the clause matrix $\mathcal T^\psi_l=\{\psi_{lii'}: i,i'\le n\}$;
--   3. $S^{\gamma,\phi}$ owns $\gamma_j,\bar\gamma_j$ ($j\le m$) and $\phi_{li}$ ($l\le L$, $i\le n$);
--   4. $S^\lambda$ owns $\lambda^k_i,\bar\lambda^k_i$ ($k=1,2$, $i\le n$).
--
--   **Bundles.** $\mathcal T^{\psi,\phi}_{li}=\{\psi_{lii'}:i'\le n\}\cup\{\phi_{li}\}$ (the $i$-th row plus $\phi_{li}$), $\mathcal F^\psi_{li}=\{\psi_{li'i}:i'\le n\}$ (the $i$-th column), $\mathcal F^{\psi,\phi}_l=\mathcal T^\psi_l\cup\{\phi_{l1},\dots,\phi_{ln}\}$, $\mathcal K_l=\{\chi_i\}\cup\mathcal T^{\psi,\phi}_{li}$, $\bar{\mathcal K}_l=\{\bar\chi_i\}\cup\mathcal T^{\psi,\phi}_{li}$, $\mathcal M_i=\{\chi_i,\lambda^1_i,\lambda^2_i\}\cup\bigcup_{x_i\in C_l}\mathcal F^\psi_{li}$ and $\bar{\mathcal M}_i=\{\bar\chi_i,\bar\lambda^1_i,\bar\lambda^2_i\}\cup\bigcup_{\bar x_i\in C_l}\mathcal F^\psi_{li}$.
--
--   **Buyers** (budget; XOR valuation):
--
--   1. $B^{\mathcal K}_i$: $V+T$; $W$ for each $\mathcal K_l$ and each $\bar{\mathcal K}_l$, $l\le L$;
--   2. $B^{\mathcal M}_i$: $2V$; $2V$ for $\mathcal M_i$ and for $\bar{\mathcal M}_i$;
--   3. $B^{\chi,1}_i$, $B^{\chi,2}_i$: $V$; $V$ for $\{\chi_i\}$ and for $\{\bar\chi_i\}$;
--   4. $B^{\lambda,1}_i$: $U$; $V$ for $\{\lambda^1_i\}$, $V-L$ for $\{\bar\lambda^1_i\}$;
--   5. $B^{\lambda,2}_i$: $U$; $V-L$ for $\{\lambda^2_i\}$, $V$ for $\{\bar\lambda^2_i\}$;
--   6. $B^{\mathcal G}_j$ ($j\le m$): $L$; with $\mathcal G_{jl}=\{\gamma_j\}\cup\mathcal F^{\psi,\phi}_l$ for the terms containing $\bar y_j$ and $\bar{\mathcal G}_{lj}=\{\bar\gamma_j\}\cup\mathcal F^{\psi,\phi}_l$ for the terms containing $y_j$, its value for a package $S$ is
--   $$
--   \max\big(\#\{l:\mathcal G_{jl}\subseteq S\},\ \#\{l:\bar{\mathcal G}_{lj}\subseteq S\}\big).
--   $$
--
--   The constants are **admissible** if $0\le T$, $nT<1$, $U>nL$, $V>4U$, $W>7nV$. An **$nW$-equilibrium** is a core outcome of $\mathrm{CEx}_\varphi$ with welfare at least $nW$. In an outcome, **$B^{\mathcal M}$ blocks the clause $C_l$** if some $B^{\mathcal M}_i$ obtains a column $\mathcal F^\psi_{li}$, and an assignment $y$ **falsifies** $C_l$ if some $y$-literal of $C_l$ is false under $y$.
--
--   This is the construction of Appendix A.3, whose core outcomes of welfare $\ge nW$ correspond to the witnesses $x$ of $\exists x\forall y\,\varphi(x,y)$.
--
--   **Formalization Note** Misprints of A.3 are resolved from the figures and the text: the row/column bundles follow Figure 2 (p.30), Figure 1 (p.27) and p.28 (the printed $\mathcal F^\psi_{li}=\{\psi_{lii'}\}$ is transposed; the transposed reading gives an isomorphic exchange); $\mathcal F^{\psi,\phi}_l$ is the box of Figure 2; the value of $B^{\mathcal G}_j$ is the count of its bundles, as the "i.e." and Table 6 say (the printed fraction $(\max\{|\mathcal G_l|,|\bar{\mathcal G}_l|\}-1)/(n(n+1))$ contradicts them); $B^{\lambda,2}_i$ follows the bullet on p.30, not Table 6. The value of $B^{\mathcal G}_j$ is two groups of the bid language. Items, buyers and sellers are finite sum types indexed by `Fin n`, `Fin m`, `Fin L`; $\lambda^1,\lambda^2$ are `lam 0`, `lam 1`.
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Appendix A.3, pp.29–31 (sellers p.29, bundles p.29, buyers pp.29–31, Figure 2 p.30, Table 6 p.31; constants p.29); Figure 1 p.27 and A.2 p.28 (rows and columns); A.4, p.31 (nW-equilibrium); p.30 (blocking by Bᴹ)

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore
import Definitions.Def_BudgetCoreExchange_QSAT2

namespace BudgetCoreExchange

/-- The kinds of buyers indexed by `i = 1, …, n` in the exchange `CEx_ϕ` (Appendix A.3,
pp.29–31): `Bᴷᵢ`, `Bᴹᵢ`, `B^{χ,1}ᵢ`, `B^{χ,2}ᵢ`, `B^{λ,1}ᵢ`, `B^{λ,2}ᵢ`. -/
inductive BKind where
  | K
  | M
  | chi1
  | chi2
  | lam1
  | lam2
  deriving DecidableEq

instance : Fintype BKind where
  elems := {BKind.K, BKind.M, BKind.chi1, BKind.chi2, BKind.lam1, BKind.lam2}
  complete := by intro x; cases x <;> simp

namespace DNF

/-- The number `L` of terms (clauses `C₁, …, C_L`) of `ϕ`. -/
abbrev numTerms (ϕ : DNF) : ℕ := ϕ.terms.length

/-- The term `C_l` of `ϕ`. -/
def term (ϕ : DNF) (l : Fin ϕ.numTerms) : List (Lit ϕ.n ϕ.m) := ϕ.terms.get l

end DNF

/-- The items of `CEx_ϕ` (Appendix A.3, p.29): `χᵢ, χ̄ᵢ` (`Fin n × Bool`, `true` unbarred);
`ψ_{lii'}` (`Fin L × Fin n × Fin n`); `γⱼ, γ̄ⱼ` (`Fin m × Bool`); `φ_{li}` (`Fin L × Fin n`);
`λᵏᵢ, λ̄ᵏᵢ`, `k = 1, 2` (`Fin 2 × Fin n × Bool`). -/
abbrev GItem (ϕ : DNF) : Type :=
  (Fin ϕ.n × Bool) ⊕ (Fin ϕ.numTerms × Fin ϕ.n × Fin ϕ.n) ⊕ (Fin ϕ.m × Bool) ⊕
    (Fin ϕ.numTerms × Fin ϕ.n) ⊕ (Fin 2 × Fin ϕ.n × Bool)

/-- The buyers of `CEx_ϕ` (Appendix A.3, pp.29–31): the six kinds indexed by `i = 1, …, n`, and
`Bᴳⱼ`, `j = 1, …, m`. -/
abbrev GBuyer (ϕ : DNF) : Type := (BKind × Fin ϕ.n) ⊕ Fin ϕ.m

/-- The `n + L + 2` sellers of `CEx_ϕ` (Appendix A.3, p.29): `Sχᵢ` (`Fin n`), `Sψ_l` (`Fin L`),
`S^{γ,φ}` and `Sλ`. -/
abbrev GSeller (ϕ : DNF) : Type := Fin ϕ.n ⊕ Fin ϕ.numTerms ⊕ Unit ⊕ Unit

set_option synthInstance.maxSize 1024 in
instance (ϕ : DNF) : DecidableEq (GItem ϕ) := by unfold GItem; infer_instance
set_option synthInstance.maxSize 1024 in
instance (ϕ : DNF) : Fintype (GItem ϕ) := by unfold GItem; infer_instance
instance (ϕ : DNF) : DecidableEq (GBuyer ϕ) := by unfold GBuyer; infer_instance
instance (ϕ : DNF) : Fintype (GBuyer ϕ) := by unfold GBuyer; infer_instance
instance (ϕ : DNF) : DecidableEq (GSeller ϕ) := by unfold GSeller; infer_instance
instance (ϕ : DNF) : Fintype (GSeller ϕ) := by unfold GSeller; infer_instance

namespace Gadget

variable {ϕ : DNF}

/-- The item `χᵢ`. -/
def chi (i : Fin ϕ.n) : GItem ϕ := Sum.inl (i, true)
/-- The item `χ̄ᵢ`. -/
def chiBar (i : Fin ϕ.n) : GItem ϕ := Sum.inl (i, false)
/-- The item `ψ_{lii'}`. -/
def psi (l : Fin ϕ.numTerms) (i i' : Fin ϕ.n) : GItem ϕ := Sum.inr (Sum.inl (l, i, i'))
/-- The item `γⱼ`. -/
def gam (j : Fin ϕ.m) : GItem ϕ := Sum.inr (Sum.inr (Sum.inl (j, true)))
/-- The item `γ̄ⱼ`. -/
def gamBar (j : Fin ϕ.m) : GItem ϕ := Sum.inr (Sum.inr (Sum.inl (j, false)))
/-- The item `φ_{li}`. -/
def phi (l : Fin ϕ.numTerms) (i : Fin ϕ.n) : GItem ϕ := Sum.inr (Sum.inr (Sum.inr (Sum.inl (l, i))))
/-- The item `λᵏᵢ` (`k = 0` is `λ¹`, `k = 1` is `λ²`). -/
def lam (k : Fin 2) (i : Fin ϕ.n) : GItem ϕ := Sum.inr (Sum.inr (Sum.inr (Sum.inr (k, i, true))))
/-- The item `λ̄ᵏᵢ` (`k = 0` is `λ̄¹`, `k = 1` is `λ̄²`). -/
def lamBar (k : Fin 2) (i : Fin ϕ.n) : GItem ϕ :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (k, i, false))))

/-- The buyer `Bᴷᵢ`. -/
def BK (i : Fin ϕ.n) : GBuyer ϕ := Sum.inl (BKind.K, i)
/-- The buyer `Bᴹᵢ`. -/
def BM (i : Fin ϕ.n) : GBuyer ϕ := Sum.inl (BKind.M, i)
/-- The buyer `Bᴳⱼ`. -/
def BG (j : Fin ϕ.m) : GBuyer ϕ := Sum.inr j
/-- The seller `Sχᵢ`. -/
def SChi (i : Fin ϕ.n) : GSeller ϕ := Sum.inl i

/-- The row `{ψ_{lii'} | i' = 1, …, n}` of the clause matrix of `C_l`, wanted by `Bᴷᵢ`. -/
def rowPsi (l : Fin ϕ.numTerms) (i : Fin ϕ.n) : Finset (GItem ϕ) :=
  Finset.univ.image fun i' => psi l i i'

/-- `T^{ψ,φ}_{li}`: the row of `Bᴷᵢ` in the clause matrix of `C_l`, together with `φ_{li}`
(Appendix A.3, p.29, read with Figure 2, p.30). -/
def Tpf (l : Fin ϕ.numTerms) (i : Fin ϕ.n) : Finset (GItem ϕ) :=
  insert (phi l i) (rowPsi l i)

/-- `F^ψ_{li}`: the column `{ψ_{li'i} | i' = 1, …, n}` of the clause matrix of `C_l`, wanted by
`Bᴹᵢ` (Appendix A.3, p.29, read with Figure 2, p.30, and Figure 1, p.27). -/
def colPsi (l : Fin ϕ.numTerms) (i : Fin ϕ.n) : Finset (GItem ϕ) :=
  Finset.univ.image fun i' => psi l i' i

/-- `T^ψ_l = {ψ_{li'i} | i, i' = 1, …, n}`: the whole clause matrix of `C_l` (p.29). -/
def Tpsi (l : Fin ϕ.numTerms) : Finset (GItem ϕ) :=
  Finset.univ.image fun p : Fin ϕ.n × Fin ϕ.n => psi l p.1 p.2

/-- `F^{ψ,φ}_l = T^ψ_l ∪ {φ_{li} | i = 1, …, n}` (p.29, read with Figure 2, p.30). -/
def Fpf (l : Fin ϕ.numTerms) : Finset (GItem ϕ) :=
  Tpsi l ∪ Finset.univ.image fun i => phi l i

/-- `K_l := {χᵢ} ∪ T^{ψ,φ}_{li}`, a bundle `Bᴷᵢ` values at `W` (p.30). -/
def Kb (l : Fin ϕ.numTerms) (i : Fin ϕ.n) : Finset (GItem ϕ) := insert (chi i) (Tpf l i)

/-- `K̄_l := {χ̄ᵢ} ∪ T^{ψ,φ}_{li}`, a bundle `Bᴷᵢ` values at `W` (p.30). -/
def Kbar (l : Fin ϕ.numTerms) (i : Fin ϕ.n) : Finset (GItem ϕ) := insert (chiBar i) (Tpf l i)

open Classical in
/-- `Mᵢ := {χᵢ, λ¹ᵢ, λ²ᵢ} ∪ ⋃_{xᵢ ∈ C_l} F^ψ_{li}` (p.30). -/
noncomputable def Mb (i : Fin ϕ.n) : Finset (GItem ϕ) :=
  {chi i, lam 0 i, lam 1 i} ∪
    (Finset.univ.filter fun l => (Sum.inl i, true) ∈ ϕ.term l).biUnion fun l => colPsi l i

open Classical in
/-- `M̄ᵢ := {χ̄ᵢ, λ̄¹ᵢ, λ̄²ᵢ} ∪ ⋃_{x̄ᵢ ∈ C_l} F^ψ_{li}` (p.30). -/
noncomputable def Mbar (i : Fin ϕ.n) : Finset (GItem ϕ) :=
  {chiBar i, lamBar 0 i, lamBar 1 i} ∪
    (Finset.univ.filter fun l => (Sum.inl i, false) ∈ ϕ.term l).biUnion fun l => colPsi l i

/-- A plain XOR bid: each bundle `(T, w)` becomes the group `(T, [(T, w)])`. -/
def xorBid {Item : Type} (bs : List (Finset Item × ℝ)) : Bid Item ℝ :=
  bs.map fun b => ⟨b.1, [b]⟩

end Gadget

open Gadget Classical in
/-- **The exchange `CEx_ϕ`** of the reduction from QSAT₂ (Bichler–Waldherr, arXiv:1807.08253v1,
Appendix A.3, pp.29–31, with Figure 2, p.30, and Table 6, p.31), for a DNF formula `ϕ` with terms
`C₁, …, C_L` and constants `T, U, V, W`.

Sellers (p.29), each valuing every package at `0` (A.3 gives sellers no valuation):
* `Sχᵢ` owns `χᵢ, χ̄ᵢ`; `Sψ_l` owns `ψ_{lii'}` (`i, i' = 1, …, n`); `S^{γ,φ}` owns `γⱼ, γ̄ⱼ` and
  `φ_{li}`; `Sλ` owns `λᵏᵢ, λ̄ᵏᵢ` (`k = 1, 2`).

Buyers (pp.29–31), budget then XOR bids:
* `Bᴷᵢ`: budget `V + T`; value `W` for each `K_l`, `K̄_l`, `l = 1, …, L`;
* `Bᴹᵢ`: budget `2V`; value `2V` for `Mᵢ` and for `M̄ᵢ`;
* `B^{χ,1}ᵢ`, `B^{χ,2}ᵢ`: budget `V`; value `V` for `{χᵢ}` and for `{χ̄ᵢ}`;
* `B^{λ,1}ᵢ`: budget `U`; value `V` for `{λ¹ᵢ}` and `V − L` for `{λ̄¹ᵢ}`;
* `B^{λ,2}ᵢ`: budget `U`; value `V − L` for `{λ²ᵢ}` and `V` for `{λ̄²ᵢ}`;
* `Bᴳⱼ`: budget `L`; with `G_{jl} = {γⱼ} ∪ F^{ψ,φ}_l` for the terms `C_l` containing `ȳⱼ` and
  `Ḡ_{lj} = {γ̄ⱼ} ∪ F^{ψ,φ}_l` for the terms containing `yⱼ`, its value for a package `S` is
  `max(#{l : G_{jl} ⊆ S}, #{l : Ḡ_{lj} ⊆ S})` ("the maximum number of bundles of type 𝒢 and
  type 𝒢̄ he obtains", p.31), written as two groups of the bid language.

**Formalization Note.** Readings of misprints, each checked against the rendered pages:
* `T^{ψ,φ}_{li}` is the `i`-th row `{ψ_{lii'}}` plus `φ_{li}` and `F^ψ_{li}` is the `i`-th column
  `{ψ_{li'i}}`, as drawn in Figure 2 (p.30) and Figure 1 (p.27) and described on p.28 ("the i-th
  'row' … {ψ_{1i1}, …, ψ_{1in}}"); the printed formulas `T^{ψ,φ}_{li} = T^ψ_l ∪ {φ_{li}}` and
  `F^ψ_{li} = {ψ_{lii'}}` omit the row index and transpose the column. Rows and columns of one
  matrix always meet, so the transposed reading gives an isomorphic exchange.
* `F^{ψ,φ}_l` is the whole matrix plus `φ_{l1}, …, φ_{ln}` (Figure 2); the printed
  "`T^{ψ,φ}_l ∪ …`" uses an undefined symbol.
* The value of `Bᴳⱼ` is the count of the bundles obtained, as the "i.e." and Table 6 say; the
  printed fraction `(max{|G_l|, |Ḡ_l|} − 1)/(n(n+1))` contradicts both.
* `B^{λ,2}ᵢ` follows the bullet on p.30; Table 6 prints `λ¹`, `λ̄¹` for it.
* "`xᵢ ∈ C_l`" means the literal `xᵢ` occurs in the term `C_l`, "`x̄ᵢ ∈ C_l`" its negation. -/
noncomputable def gadget (ϕ : DNF) (T U V W : ℝ) :
    Exchange (GBuyer ϕ) (GSeller ϕ) (GItem ϕ) ℝ where
  endow
    | Sum.inl i => {chi i, chiBar i}
    | Sum.inr (Sum.inl l) => Tpsi l
    | Sum.inr (Sum.inr (Sum.inl ())) =>
        Finset.univ.image gam ∪ Finset.univ.image gamBar ∪
          Finset.univ.image fun p : Fin ϕ.numTerms × Fin ϕ.n => phi p.1 p.2
    | Sum.inr (Sum.inr (Sum.inr ())) =>
        Finset.univ.image (fun p : Fin 2 × Fin ϕ.n => lam p.1 p.2) ∪
          Finset.univ.image fun p : Fin 2 × Fin ϕ.n => lamBar p.1 p.2
  ask _ := []
  bid
    | Sum.inl (BKind.K, i) =>
        xorBid ((List.finRange ϕ.numTerms).flatMap fun l => [(Kb l i, W), (Kbar l i, W)])
    | Sum.inl (BKind.M, i) => xorBid [(Mb i, 2 * V), (Mbar i, 2 * V)]
    | Sum.inl (BKind.chi1, i) => xorBid [({chi i}, V), ({chiBar i}, V)]
    | Sum.inl (BKind.chi2, i) => xorBid [({chi i}, V), ({chiBar i}, V)]
    | Sum.inl (BKind.lam1, i) => xorBid [({lam 0 i}, V), ({lamBar 0 i}, V - ϕ.numTerms)]
    | Sum.inl (BKind.lam2, i) => xorBid [({lam 1 i}, V - ϕ.numTerms), ({lamBar 1 i}, V)]
    | Sum.inr j =>
        [⟨{gam j}, ((List.finRange ϕ.numTerms).filter fun l =>
            decide ((Sum.inr j, false) ∈ ϕ.term l)).map fun l => (Fpf l, (1 : ℝ))⟩,
         ⟨{gamBar j}, ((List.finRange ϕ.numTerms).filter fun l =>
            decide ((Sum.inr j, true) ∈ ϕ.term l)).map fun l => (Fpf l, (1 : ℝ))⟩]
  budget
    | Sum.inl (BKind.K, _) => V + T
    | Sum.inl (BKind.M, _) => 2 * V
    | Sum.inl (BKind.chi1, _) => V
    | Sum.inl (BKind.chi2, _) => V
    | Sum.inl (BKind.lam1, _) => U
    | Sum.inl (BKind.lam2, _) => U
    | Sum.inr _ => ϕ.numTerms

/-- The constants of the reduction are **admissible** (Appendix A.3, p.29: "Let T < 1/n, U > nL,
V > 4U and W > 7nV"): `0 ≤ T`, `nT < 1`, `U > nL`, `V > 4U`, `W > 7nV`.

**Formalization Note.** `T < 1/n` is written `nT < 1` (the theorems using it assume `n ≥ 1`);
`T ≥ 0` is the paper's reading of `T` as the budget a buyer `Bᴷᵢ` has left ("he only has a budget
of T left", p.30). -/
def Admissible (ϕ : DNF) (T U V W : ℝ) : Prop :=
  0 ≤ T ∧ (ϕ.n : ℝ) * T < 1 ∧ (ϕ.n : ℝ) * ϕ.numTerms < U ∧ 4 * U < V ∧ 7 * ϕ.n * V < W

/-- An **`nW`-equilibrium** (Appendix A.4, p.31): a core outcome of `CEx_ϕ` with welfare at least
`nW`. -/
def IsNWEquilibrium (ϕ : DNF) (T U V W : ℝ)
    (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) : Prop :=
  InCore (gadget ϕ T U V W) o ∧ (ϕ.n : ℝ) * W ≤ welfare (gadget ϕ T U V W) o

/-- In the outcome `o`, **`Bᴹ` blocks the clause `C_l`** (p.30): some buyer `Bᴹᵢ` obtains a
column `F^ψ_{li}` of the clause matrix of `C_l`. -/
def BlockedByM {ϕ : DNF} (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ))
    (l : Fin ϕ.numTerms) : Prop :=
  ∃ i : Fin ϕ.n, Gadget.colPsi l i ⊆ o.S (Gadget.BM i)

/-- The term `C_l` is **falsified by the assignment `y`** of the `y`-variables: some `y`-literal of
`C_l` is false under `y` (whatever `x` is). -/
def FalsifiedBy {ϕ : DNF} (y : Fin ϕ.m → Bool) (l : Fin ϕ.numTerms) : Prop :=
  ∃ j : Fin ϕ.m, ∃ b : Bool, (Sum.inr j, b) ∈ ϕ.term l ∧ y j ≠ b

end BudgetCoreExchange


