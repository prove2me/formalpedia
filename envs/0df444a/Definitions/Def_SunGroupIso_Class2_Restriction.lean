-- Prove2me | Definitions.Def_SunGroupIso_Class2_Restriction
-- name    : SunGroupIso_Class2_Restriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:16.450006+00:00
-- url     : https://prove2.me/theorems/f7f554c2-e1d1-409b-a6ad-df0021d9a0fa
-- title:
--   Group restrictions (Definition 4.1), restriction isomorphism (Problem 4.3) and their codes
-- statement:
--   Let $G$ be a finite $p$-group of class 2, $R=\mathbb Z/p^\tau\mathbb Z$, and $\zeta,\gamma,\kappa,\tau,\delta$ positive integers. A **group restriction** $(z_1,\dots,z_\zeta,Y,g_1,\dots,g_\gamma,F,\rho)$ of $G$ satisfies (Definition 4.1): (a) $Z(G)=\langle z_1\rangle\oplus\cdots\oplus\langle z_\zeta\rangle\oplus Y$; (b) every element of $Y$ has order at most $p^\tau$; (c) there is $K\le G/Z(G)$ with $G/Z(G)=\langle\tilde g_1\rangle\oplus\cdots\oplus\langle\tilde g_\gamma\rangle\oplus K$, every element of $K$ of order at most $p^\delta$, and every element of $K$ has a lift of order at most $p^\tau$; (d) $F=\langle g: \tilde g\in K,\ \mathrm{ord}(g)\le p^\tau\rangle$ and $\langle F,Z(G)\rangle/Z(G)=K$; (e) $\rho=0$ on $Z(G)\cap F$; (f) if $g\in F$ and $\rho(g)=0$ then $[g,F]\le\langle z_1\rangle\oplus\cdots\oplus\langle z_\zeta\rangle$; (g) $\rho(gh)=\rho(g)+\rho(h)$ on $F$. $\psi=\mathrm{rank}\,Y$, $\eta=\mathrm{rank}\,\langle F,Z(G)\rangle/Z(G)$; $\zeta_0$ is the number of $z_i$ of order greater than $p$.
--
--   A **group restriction isomorphism** (Problem 4.3) to a restriction $(z',X,g',E,\rho')$ of $H$ is an isomorphism $f$ with $f(z_i)=z'_i$, $f(g_i)=g'_i$, $f(Y)=X$, $f(F)=E$, and $\rho'(f(g))=\rho(g)$ for $g\in F$.
--
--   A label $\lambda:D_{p^\delta}(G)\to(\mathbb Z/p^\delta)^d$ **extends** to $\rho(h)=\lambda(h)p^{\tau-\delta}\in(\mathbb Z/p^\tau)^d$ (Group Restriction Construction Algorithm, step 1).
--
--   **Codes.** A restriction of a labelled group is coded as $\zeta,\gamma,\kappa$, then $\tau,\delta$ in unary, the labels of the $z_i$ and $g_i$, the membership bits of $Y$ and $F$, and the coordinates of $\rho$ on $F$; a label function by its values on $D_{p^\delta}(G)$.
--
--   **Formalization Note** $\rho$ is a function on all of $G$; only its values on $F$ enter a condition or a code. The page's reindexing "$z_1,\dots,z_{\zeta-\zeta_0}$ are of order $p$" is replaced by `bigIdx`, the increasing list of indices with $\mathrm{ord}(z_k)>p$, so no restriction is reordered.
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Definition 4.1 pp. 12–13 (PDF 14–15); Problem 4.3 p. 13 (PDF 15); p. 24 (PDF 26)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_Basic

set_option autoImplicit false

noncomputable section

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)

/-- **The data of a group restriction** (Definition 4.1, Sun 2026, arXiv:2611.05920, pp. 12–13,
PDF pp. 14–15): `(z_1, …, z_ζ, Y, g_1, …, g_γ, F, ρ)` with `ρ : F → R^κ`, `R = Z/p^τZ`. `ρ` is a
function on `G`; only its values on `F` enter any condition or code. -/
structure Restriction (G : Type*) [Group G] (p ζ γ κ τ : ℕ) where
  z : Fin ζ → G
  Y : Subgroup G
  g : Fin γ → G
  F : Subgroup G
  ρ : G → Fin κ → ZMod (p ^ τ)

variable {G H : Type*} [Group G] [Group H] {p ζ γ κ τ : ℕ}

/-- `Z = ⟨z_1⟩ ⊕ ⋯ ⊕ ⟨z_ζ⟩`. -/
def Restriction.Zpart (r : Restriction G p ζ γ κ τ) : Subgroup G := Subgroup.closure (Set.range r.z)

/-- `K = ⟨F, Z(G)⟩/Z(G)`, a subgroup of `G/Z(G)`. -/
def Restriction.Kq (r : Restriction G p ζ γ κ τ) : Subgroup (Qt G) :=
  (r.F ⊔ Subgroup.center G).map (qmap G)

/-- **Group restriction** (Definition 4.1, pp. 12–13, PDF pp. 14–15), for positive integers
`ζ, γ, κ, τ, δ`:
(a) `Z(G) = ⟨z_1⟩ ⊕ ⋯ ⊕ ⟨z_ζ⟩ ⊕ Y`; (b) every element of `Y` has order at most `p^τ`;
(c) there is `K ≤ G/Z(G)` with `G/Z(G) = ⟨g̃_1⟩ ⊕ ⋯ ⊕ ⟨g̃_γ⟩ ⊕ K`, every element of `K` of order at most
`p^δ`, and every `g̃ ∈ K` has a lift `g'` of order at most `p^τ`; (d) `F = ⟨g ∈ G : g̃ ∈ K, ord(g) ≤ p^τ⟩`
and `⟨F, Z(G)⟩/Z(G) = K`; (e) `ρ = 0` on `Z(G) ∩ F`; (f) if `g ∈ F` and `ρ(g) = 0` then
`[g, F] ≤ ⟨z_1⟩ ⊕ ⋯ ⊕ ⟨z_ζ⟩`; (g) `ρ(gh) = ρ(g) + ρ(h)` on `F`. -/
def IsRestriction (p δ : ℕ) (r : Restriction G p ζ γ κ τ) : Prop :=
  0 < ζ ∧ 0 < γ ∧ 0 < κ ∧ 0 < τ ∧ 0 < δ ∧
  DecompWith (Subgroup.center G) r.z r.Y ∧
  (∀ y ∈ r.Y, orderOf y ≤ p ^ τ) ∧
  (∃ K : Subgroup (Qt G),
    DecompWith ⊤ (fun i => tl (r.g i)) K ∧
    (∀ x ∈ K, orderOf x ≤ p ^ δ) ∧
    (∀ x ∈ K, ∃ g' : G, tl g' = x ∧ orderOf g' ≤ p ^ τ) ∧
    r.F = Subgroup.closure {g | tl g ∈ K ∧ orderOf g ≤ p ^ τ} ∧
    r.Kq = K) ∧
  (∀ x ∈ r.F, x ∈ Subgroup.center G → r.ρ x = 0) ∧
  (∀ x ∈ r.F, r.ρ x = 0 →
    Subgroup.closure {c | ∃ y ∈ r.F, c = ⁅x, y⁆} ≤ r.Zpart) ∧
  (∀ x ∈ r.F, ∀ y ∈ r.F, r.ρ (x * y) = r.ρ x + r.ρ y)

/-- **Group restriction isomorphism** (Problem 4.3, p. 13, PDF p. 15): an isomorphism `f : G → H` with
`f(z_i) = z'_i`, `f(g_i) = g'_i`, `f(Y) = X`, `f(F) = E` and `ρ'(f(g)) = ρ(g)` for `g ∈ F`. -/
def IsRestrictionIso (r : Restriction G p ζ γ κ τ) (r' : Restriction H p ζ γ κ τ) (f : G ≃* H) :
    Prop :=
  (∀ i, f (r.z i) = r'.z i) ∧ (∀ i, f (r.g i) = r'.g i) ∧
  r.Y.map f.toMonoidHom = r'.Y ∧ r.F.map f.toMonoidHom = r'.F ∧
  ∀ x ∈ r.F, r'.ρ (f x) = r.ρ x

/-- `ψ = rank Y` (p. 13). -/
def Restriction.psi (r : Restriction G p ζ γ κ τ) : ℕ := abRank r.Y

/-- `η = rank ⟨F, Z(G)⟩/Z(G)` (p. 13). -/
def Restriction.eta (r : Restriction G p ζ γ κ τ) : ℕ := abRank r.Kq

/-- The coefficients of a central element on `z_1, …, z_ζ` in `Z(G) = ⟨z_1⟩ ⊕ ⋯ ⊕ ⟨z_ζ⟩ ⊕ Y`
(its "projection onto `z_1, …, z_ζ`"). -/
def Restriction.zCo (r : Restriction G p ζ γ κ τ) (x : G) : Fin ζ → ℕ := coeffsWith r.z r.Y x

/-- The indices `k` (zero-based, increasing) with `ord(z_k) > p`; there are `ζ_0` of them (§5.1,
p. 27, PDF p. 29: "ζ_0 the number of elements in `z_1, …, z_ζ` of order greater than `p`"). -/
def Restriction.bigList (p : ℕ) (r : Restriction G p ζ γ κ τ) : List (Fin ζ) :=
  (List.finRange ζ).filter fun i => p < orderOf (r.z i)

/-- `ζ_0`. -/
def Restriction.zeta0 (r : Restriction G p ζ γ κ τ) : ℕ := (r.bigList p).length

/-- The `j`-th (one-based) index with `ord(z_k) > p`, zero-based; the page's `ζ − ζ_0 + j` after its
reindexing "`z_1, …, z_{ζ−ζ_0}` are of order `p`". -/
def Restriction.bigIdx (r : Restriction G p ζ γ κ τ) (j : ℕ) : ℕ :=
  match (r.bigList p)[j - 1]? with
  | some i => i.val
  | none => ζ

/-- `z_{ζ−ζ_0+j}` in the page's reindexing: the `j`-th generator of order greater than `p`. -/
def Restriction.zBig (r : Restriction G p ζ γ κ τ) (j : ℕ) : G := at1 r.z (r.bigIdx j + 1)

/-- `⊕_{i=ζ−ζ_0+1}^{ζ} ⟨z_i⟩`: the summands of order greater than `p`. -/
def Restriction.Zbig (r : Restriction G p ζ γ κ τ) : Subgroup G :=
  Subgroup.closure {x | ∃ i, p < orderOf (r.z i) ∧ x = r.z i}

/-- `⟨z_1⟩ ⊕ ⋯ ⊕ ⟨z_{ζ−ζ_0}⟩`: the summands of order at most `p`. -/
def Restriction.Zsmall (r : Restriction G p ζ γ κ τ) : Subgroup G :=
  Subgroup.closure {x | ∃ i, orderOf (r.z i) ≤ p ∧ x = r.z i}

/-- The code of a group restriction of a labelled group: `ζ, γ, κ` in binary, `τ, δ` in unary, the
labels of `z_1, …, z_ζ` and of `g_1, …, g_γ`, the membership bits of `Y` and of `F`, and for every
element of `F` (label order) the `κ` coordinates of `ρ`, each in `[0, p^τ)`. -/
def encRestriction {N : ℕ} (e : G ≃ Fin N) (δ : ℕ) (r : Restriction G p ζ γ κ τ) : List Bool :=
  encodeNat ζ ++ encodeNat γ ++ encodeNat κ ++ encUnary τ ++ encUnary δ ++
    encVec (encElem e) r.z ++ encVec (encElem e) r.g ++ encSet e r.Y ++ encSet e r.F ++
    encOn e r.F (fun x => encVec encZMod (r.ρ x))

/-- The extension of a label `λ : D_{p^δ}(G) → (Z/p^δZ)^d` to `ρ(h) = λ(h) · p^{τ−δ} ∈ (Z/p^τZ)^d`
(Group Restriction Construction Algorithm, step 1, p. 24, PDF p. 26). -/
def extLabel (p δ τ : ℕ) {d : ℕ} (lam : G → Fin d → ZMod (p ^ δ)) : G → Fin d → ZMod (p ^ τ) :=
  fun h s => ((lam h s).val : ZMod (p ^ τ)) * (p : ZMod (p ^ τ)) ^ (τ - δ)

/-- The code of a label function on `D_{p^δ}(G)`: its values on `D_{p^δ}(G)` in label order. -/
def encLabel {N : ℕ} (e : G ≃ Fin N) (p δ : ℕ) {d : ℕ} (lam : G → Fin d → ZMod (p ^ δ)) : List Bool :=
  encOn e (Dsub p δ G) (fun x => encVec encZMod (lam x))

end SunGroupIso.Class2


