-- Prove2me | Definitions.Def_ImplicitParityWL_SeedDescription
-- name    : ImplicitParityWL_SeedDescription
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:59.687891+00:00
-- url     : https://prove2.me/theorems/2edae72c-0cfa-4127-b959-ad36d8d20ca3
-- title:
--   Seed descriptions, track bits and the maps (14)–(16)
-- statement:
--   Let $|\mathcal A|\le k+1$ and let $\alpha:\mathrm{Var}(\mathcal A)\to\mathbb F_2$. A **seed description** for $\mathcal A$ realizing $\alpha$ consists of partial seeds $z_v\in\mathbb F_2^{I_v}$ and masks $x_{e,1},\dots,x_{e,k+2}\in\mathrm{rowspan}(B_e)$ such that $a\cdot z_v=\alpha(X_{v,a})$ for all $X_{v,a}\in\mathrm{Var}(\mathcal A)$, $x\cdot z_v=0$ for all block-even $x\in C$ with $\mathrm{supp}(x)\subseteq I_v$, an initialized location has the seed $\iota(v)$ on the first block and zero elsewhere, and
--   $$
--   \sum_{h=1}^{k+2}x_{e,h}(c)=z_u(\sigma(c))+z_v(\tau(c))+z_w(\pi(c))\quad\text{for all }c\in I_e,
--   $$
--   omitting the last summand for a binary schema. The **track bits** are $t_{e,0}(c)=z_u(\sigma(c))$ for a binary schema, $t_{e,0}(c)=z_u(\sigma(c))+z_v(\tau(c))$ for a ternary one, and $t_{e,h}(c)=t_{e,0}(c)+\sum_{i=1}^hx_{e,i}(c)$. The maps from $G_0$ to $G_1$ are
--   $$
--   \mathrm{msk}_{e,h}[x]\mapsto\mathrm{msk}_{e,h}[x+x_{e,h}],\qquad \mathrm{crd}_{v,c}[s]\mapsto\mathrm{crd}_{v,c}[s+z_v(c)],\qquad \mathrm{trk}_{e,h,c}[s]\mapsto\mathrm{trk}_{e,h,c}[s+t_{e,h}(c)],
--   $$
--   $$
--   \mathrm{upd}_{e,h,c}[s,t]\mapsto\mathrm{upd}_{e,h,c}[s+t_{e,h-1}(c),t+t_{e,h}(c)],\quad \mathrm{sum}_{e,c}[s]\mapsto\mathrm{sum}_{e,c}[s+t_{e,0}(c)],
--   $$
--   $$
--   \mathrm{junc}_{e,c}[s,t,s+t]\mapsto\mathrm{junc}_{e,c}[s+z_u(\sigma(c)),t+z_v(\tau(c)),s+t+t_{e,0}(c)].
--   $$
--   Duplicator's bijections in the proof of Theorem 5.14 are these maps.
--
--   **Formalization Note** Seeds and masks are total functions of which only the relevant values are read. The bound $|\mathcal A|\le k+1$ is a binder of Lemma 5.12.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Definition 5.10, pp.30–31; eqs. (13)–(16), pp.30–33

import Mathlib
import Definitions.Def_ImplicitParityWL_Exposure

namespace ImplicitParityWL

/-- The data of a seed description `D = ((z_v)_{v∈W}, (x_{e,h})_{e∈E,1≤h≤k+2})` (Curticapean, Liu, Neuen, Seppelt,
*Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026,
Definition 5.10, p.30).

**Formalization Note** A partial seed `z_v ∈ 𝔽₂^{I_v}` is a total function of which only the values on `I_v` are
read, and `x e h` is read only for `1 ≤ h ≤ k + 2`. -/
structure SeedData (k ℓ : ℕ) (W E : Type*) where
  /-- The partial seeds. -/
  z : W → Word k ℓ
  /-- The masks. -/
  x : E → ℕ → Word k ℓ

namespace ImplicitSystem

variable {k ℓ : ℕ} {W E : Type*} (I : ImplicitSystem k ℓ W E)

/-- The data `D` is a **seed description for `A` realizing `α`** (Definition 5.10, p.30):

1. `a · z_v = α(X_{v,a})` for all `X_{v,a} ∈ Var(A)`;
2. `x · z_v = 0` for all block-even `x ∈ C` with `supp(x) ⊆ I_v`;
3. at an initialized location the seed is that of Example 4.11: `ι(v)` on the first block and zero elsewhere;
4. the masks `x_{e,1}, …, x_{e,k+2}` lie in `rowspan(B_e)`;
5. the mask-sum condition (13): `∑_h x_{e,h}(c) = z_u(σ(c)) + z_v(τ(c)) + z_w(π(c))` for all `c ∈ I_e`, omitting the
   last summand for a binary schema. -/
structure IsSeedDescription (A : Finset (CColor k ℓ W E)) (α : W × Address k ℓ → ZMod 2)
    (D : SeedData k ℓ W E) : Prop where
  value : ∀ X ∈ I.Var A, X.2.dot (D.z X.1) = α X
  even : ∀ (v : W) (x : Word k ℓ), x.IsBlockEven → (x.supp : Set (Coord k ℓ)) ⊆ I.Iv A v →
    x.dot (D.z v) = 0
  init : ∀ (v : W) (b : ZMod 2), I.init v = some b → ∀ c ∈ I.Iv A v,
    D.z v c = if c.1.val = 0 then b else 0
  mask : ∀ (e : E) (h : ℕ), 1 ≤ h → h ≤ k + 2 → D.x e h ∈ maskSpace (I.schema e).dom
  mask_sum : ∀ (e : E), ∀ c ∈ I.Ie A e,
    ∑ h ∈ Finset.Icc 1 (k + 2), D.x e h c =
      D.z (I.schema e).u ((I.schema e).σ c) + D.z (I.schema e).v ((I.schema e).τ c) +
        match (I.schema e).third with
        | none => 0
        | some (w, π) => D.z w (π c)

/-- The track bits (Definition 5.10, p.31): `t_{e,0}(c) = z_u(σ(c))` for a binary schema,
`t_{e,0}(c) = z_u(σ(c)) + z_v(τ(c))` for a ternary one, and `t_{e,h}(c) = t_{e,0}(c) + ∑_{i=1}^h x_{e,i}(c)`. -/
def trackBit (D : SeedData k ℓ W E) (e : E) (h : ℕ) (c : Coord k ℓ) : ZMod 2 :=
  (match (I.schema e).third with
    | none => D.z (I.schema e).u ((I.schema e).σ c)
    | some _ => D.z (I.schema e).u ((I.schema e).σ c) + D.z (I.schema e).v ((I.schema e).τ c)) +
    ∑ i ∈ Finset.Icc 1 h, D.x e i c

/-- The maps (14), (15) and (16) of §5.3.2, pp.31 and 33, from the vertex names of `G₀` to those of `G₁`:

* (14) `msk_{e,h}[x] ↔ msk_{e,h}[x + x_{e,h}]`;
* (15) `crd_{v,c}[s] ↔ crd_{v,c}[s + z_v(c)]`;
* (16) `trk_{e,h,c}[s] ↔ trk_{e,h,c}[s + t_{e,h}(c)]`, `upd_{e,h,c}[s, t] ↔ upd_{e,h,c}[s + t_{e,h-1}(c), t + t_{e,h}(c)]`,
  `sum_{e,c}[s] ↔ sum_{e,c}[s + t_{e,0}(c)]` and
  `junc_{e,c}[s, t, s + t] ↔ junc_{e,c}[s + z_u(σ(c)), t + z_v(τ(c)), s + t + t_{e,0}(c)]`.

**Formalization Note** The third bracket of a junction is not stored. Its value `s + t + t_{e,0}(c)` in (16) is the
sum of the first two, since `t_{e,0}(c) = z_u(σ(c)) + z_v(τ(c))` for a ternary schema. -/
def seedMap (D : SeedData k ℓ W E) : Vtx k ℓ W E → Vtx k ℓ W E
  | .msk e h x => .msk e h (x + D.x e h)
  | .crd v c s => .crd v c (s + D.z v c)
  | .trk e h c s => .trk e h c (s + I.trackBit D e h c)
  | .upd e h c s t => .upd e h c (s + I.trackBit D e (h - 1) c) (t + I.trackBit D e h c)
  | .sum e c s => .sum e c (s + I.trackBit D e 0 c)
  | .junc e c s t => .junc e c (s + D.z (I.schema e).u ((I.schema e).σ c))
      (t + D.z (I.schema e).v ((I.schema e).τ c))

end ImplicitSystem

end ImplicitParityWL


