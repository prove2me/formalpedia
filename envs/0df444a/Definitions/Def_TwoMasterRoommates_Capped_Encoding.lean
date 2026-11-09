-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Encoding
-- name    : TwoMasterRoommates_Capped_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:32:14.52004+00:00
-- url     : https://prove2.me/theorems/7e898671-cfd6-455c-a321-f100e346f4d4
-- title:
--   Integer presentation, input memory, and decision-with-witness output
-- statement:
--   For an integer-ranked instance on $n$ identities, the input is a list beginning with $n$, followed by all observer-class flags, the two master-rank arrays, and two cells per cap. A finite cap $k$ is encoded as $(1,k)$ and an infinite cap as $(0,0)$. Class $A$ has flag one. Every array follows identity order. The initial local frame is zero and this list occupies consecutive memory cells from zero.
--
--   The entry instruction calls procedure zero. An output state with local register zero equal to zero reports that no solution exists. A positive register value $p$ instead identifies $n$ consecutive memory cells, all below the supplied space limit $S$, which contain an actual solution matching:
--
--   $$\sigma.\mathrm{mem}(p+v)=M(v)\qquad(v\in V).$$
--
--   Both branches include their full mathematical correctness condition against the original weak instance. The positive branch also requires $p+n\le S$. These predicates express both decision and construction, including the empty instance, in the published costed language.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), pp. 1 and 12 (PDF pp. 2 and 13), Theorems 1.1 and B.1; p. 18 (PDF p. 19), §B.7; encoding convention for those algorithmic claims

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Instance
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

def encodeCap (k : WithTop ℤ) : List ℤ :=
  if k = ⊤ then [0, 0] else [1, k.untopD 0]

def encode {n : ℕ} (J : Instance ℤ n) : List ℤ :=
  [(n : ℤ)] ++ (List.ofFn fun v => if J.isA v then (1 : ℤ) else 0) ++
  List.ofFn J.a ++ List.ofFn J.b ++ (List.ofFn J.κ).flatMap encodeCap

def start {n : ℕ} (J : Instance ℤ n) : Light.State := ⟨Light.frame [], Light.memOf (encode J)⟩

def entry : Light.Stmt := .call 0 [] 0

def Reports {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (S : ℕ) (σ : Light.State) : Prop :=
  (σ.loc 0 = 0 ∧ ¬ ∃ M, IsSolution I M) ∨
  (0 < σ.loc 0 ∧ σ.loc 0 + (n : ℤ) ≤ (S : ℤ) ∧
    ∃ M, IsSolution I M ∧ ∀ v, σ.mem ((σ.loc 0).toNat + v.val) = (M v).val)

end TwoMasterRoommates.Capped


