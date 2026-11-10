-- Prove2me | Definitions.Def_EFXCounterex_Submodular_Instance
-- name    : EFXCounterex_Submodular_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:44:32.773388+00:00
-- url     : https://prove2.me/theorems/4ea275b4-808b-4363-8e1c-69bd9dd2fcff
-- title:
--   The three-agent, eight-good instance: types, the pair valuations $u$ (table (2)), the final valuations $v$ (display (3)), exceptional triples and the forced allocation (4)
-- statement:
--   The instance of §3.1.1 (pp. 7–9).
--
--   - **Goods** $M=\{A_1,A_2,B_1,B_2,C_1,C_2,x,y\}$ are `Fin 8` in this order (`gx = 6`, `gy = 7`); `kind g` is the type of $g$: `typ 0`, `typ 1`, `typ 2` for $A,B,C$, or `x`, `y`. `typeGoods t` is the set of the two goods of type $t$. **Agents** $a,b,c$ are `Fin 3` $=0,1,2$, agent $t$ associated with type `typ t`.
--   - **Pair values** (table (2)): for agent $i$ with own type $T$ and other types $U,V$, a pair of goods is worth $Ty\mapsto6$, $UV\mapsto5$, $Tx\mapsto4$, $Uy,Vy\mapsto3$, $TU,TV\mapsto2$, and $1$ for $TT,UU,VV,Ux,Vx,xy$ (`pairVal`).
--   - **Pair valuations** $u_i$: $u_i(\emptyset)=0$, $u_i(\{g\})=1$, and for $|S|\ge2$, $u_i(S)$ is the largest pair value over pairs of distinct goods of $S$.
--   - **Exceptional triple** of agent $i$ (`IsExceptionalTriple i T`): a three-good bundle containing $x$ and one good of each type other than $i$'s, i.e. $BCx$ for $a$, $ACx$ for $b$, $ABx$ for $c$.
--   - **Final valuations** (display (3)): $v_i(S)=7$ if $S$ contains an exceptional triple of $i$, else $v_i(S)=u_i(S)$.
--   - **Forced allocation** (display (4), up to relabelling; `IsForcedAllocation X`): for some permutation $\sigma$ of the agents, acting on their types simultaneously and fixing $x,y$, and some choice of copies $a_1\ne a_2$ of type $\sigma(A)$ and $b_1\ne b_2$ of type $\sigma(B)$: $X_{\sigma(a)}=\{a_1,y\}$, $X_{\sigma(b)}=\{b_1,x\}\cup\{\text{both }\sigma(C)\text{-goods}\}$, $X_{\sigma(c)}=\{a_2,b_2\}$. At $\sigma=\mathrm{id}$ this is $Ay\mid BCCx\mid AB$.
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), §3.1.1, table (2), displays (3) and (4), pp. 7–9

import Mathlib

namespace EFXCounterex.Submodular

/-- §3.1.1, p. 7: the kind of a good. `typ t` is one of the three types `A, B, C` (indexed by
`t : Fin 3`, with `A = 0`, `B = 1`, `C = 2`); `x` and `y` are the two single goods. Agent `t`
of `N = {a, b, c} = Fin 3` is associated with type `typ t` (`a ↔ A`, `b ↔ B`, `c ↔ C`). -/
inductive GoodKind
  | typ (t : Fin 3)
  | x
  | y
  deriving DecidableEq

/-- §3.1.1, p. 7: the eight goods `M = {A1, A2, B1, B2, C1, C2, x, y}` as `Fin 8`, in this order
(`A1 = 0, A2 = 1, B1 = 2, B2 = 3, C1 = 4, C2 = 5, x = 6, y = 7`), and the map sending each good to
its kind: goods `2t` and `2t + 1` are the two goods of type `t`. -/
def kind : Fin 8 → GoodKind :=
  ![.typ 0, .typ 0, .typ 1, .typ 1, .typ 2, .typ 2, .x, .y]

/-- The good `x` (index 6). -/
def gx : Fin 8 := 6

/-- The good `y` (index 7). -/
def gy : Fin 8 := 7

/-- The two goods of type `t`. -/
def typeGoods (t : Fin 3) : Finset (Fin 8) :=
  Finset.univ.filter fun g => kind g = .typ t

/-- Table (2), p. 8: the value `u_i` of a two-good bundle whose goods have kinds `k₁, k₂`, for
agent `i` with associated type `T = typ i` and other two types `U, V`:
`Ty ↦ 6`, `UV ↦ 5`, `Tx ↦ 4`, `Uy, Vy ↦ 3`, `TU, TV ↦ 2`, and
`TT, UU, VV, Ux, Vx, xy ↦ 1`. (The kinds `x x` and `y y` never occur in a pair of distinct
goods.) -/
def pairVal (i : Fin 3) : GoodKind → GoodKind → ℕ
  | .typ s, .y => if s = i then 6 else 3
  | .y, .typ s => if s = i then 6 else 3
  | .typ s, .x => if s = i then 4 else 1
  | .x, .typ s => if s = i then 4 else 1
  | .typ s, .typ t => if s = t then 1 else if s = i ∨ t = i then 2 else 5
  | _, _ => 1

/-- §3.1.1, p. 8: the pair valuations `u_i`. `u_i(∅) = 0`, `u_i({g}) = 1` for every good `g`,
and for a bundle of at least two goods `u_i(S)` is the value of its best pair (the maximum of
table (2) over the ordered pairs of distinct goods of `S`). -/
def u (i : Fin 3) (S : Finset (Fin 8)) : ℝ :=
  if S.card = 0 then 0
  else if S.card = 1 then 1
  else ((S.offDiag.sup fun p => pairVal i (kind p.1) (kind p.2) : ℕ) : ℝ)

/-- §3.1.1, p. 8: `T` is a triple of type `UVx` for agent `i` (its exceptional triple), where
`U, V` are the two types other than `i`'s own: `T` has three goods, contains `x`, and contains a
good of each type other than `i`'s. (Exceptional triples: `BCx` for `a`, `ACx` for `b`, `ABx`
for `c`.) -/
def IsExceptionalTriple (i : Fin 3) (T : Finset (Fin 8)) : Prop :=
  T.card = 3 ∧ gx ∈ T ∧ ∀ t : Fin 3, t ≠ i → ∃ g ∈ T, kind g = .typ t

instance (i : Fin 3) (T : Finset (Fin 8)) : Decidable (IsExceptionalTriple i T) := by
  unfold IsExceptionalTriple; infer_instance

/-- Display (3), p. 8: the final valuations `v_i(S) = 7` if `S` contains a triple of type `UVx`
(agent `i`'s exceptional triple), and `v_i(S) = u_i(S)` otherwise. -/
def v (i : Fin 3) (S : Finset (Fin 8)) : ℝ :=
  if ∃ T ∈ S.powerset, IsExceptionalTriple i T then 7 else u i S

/-- Display (4), p. 9, up to simultaneously relabelling types and agents: `X` is the allocation
`Ay (agent a) | BCCx (agent b) | AB (agent c)` after relabelling the agents and their associated
types by a permutation `σ` of `{a, b, c}` (fixing `x, y`) and choosing which copy of each type
goes where. That is, for some `σ`, agent `σ a` gets one `σ(A)`-good `a₁` and `y`, agent `σ b` gets
one `σ(B)`-good `b₁`, both `σ(C)`-goods and `x`, and agent `σ c` gets the other `σ(A)`-good `a₂`
and the other `σ(B)`-good `b₂`. -/
def IsForcedAllocation (X : Fin 3 → Finset (Fin 8)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∃ a₁ a₂ b₁ b₂ : Fin 8,
    kind a₁ = .typ (σ 0) ∧ kind a₂ = .typ (σ 0) ∧ a₁ ≠ a₂ ∧
    kind b₁ = .typ (σ 1) ∧ kind b₂ = .typ (σ 1) ∧ b₁ ≠ b₂ ∧
    X (σ 0) = {a₁, gy} ∧
    X (σ 1) = insert b₁ (insert gx (typeGoods (σ 2))) ∧
    X (σ 2) = {a₂, b₂}

end EFXCounterex.Submodular


