-- Prove2me | Definitions.Def_TDLC_Solution
-- name    : TDLC_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:23:49.518068+00:00
-- url     : https://prove2.me/theorems/a2c5e94d-9cc4-41a2-83f4-2909a0c8d117
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Arthur Freitas Ramos, Daniel O. Martinez-Rivillas, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/two-dimensional-lambda-calculus-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Certified naturality and obstruction to unrestricted naturality in a typed two-dimensional lambda calculus development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean

set_option autoImplicit true
namespace TDLC
universe u
inductive Step : {α : Type u} → α → α → Type (u + 1) where
  | beta {A B : Type u} (f : A → B) (a : A) :
      Step ((fun x => f x) a) (f a)
  | eta {A B : Type u} (f : A → B) :
      Step (fun x => f x) f
  | apCong {A B : Type u} (f : A → B) {x y : A} :
      Step x y → Step (f x) (f y)
  | lamCong {A B : Type u} {f g : A → B} :
      ((x : A) → Step (f x) (g x)) → Step f g
  | refl {A : Type u} (x : A) : Step x x
  | sym {A : Type u} {x y : A} : Step x y → Step y x
  | trans {A : Type u} {x y z : A} : Step x y → Step y z → Step x z
inductive Path : {α : Type u} → α → α → Type (u + 1) where
  | nil {A : Type u} (x : A) : Path x x
  | seq {A : Type u} {x y z : A} : Step x y → Path y z → Path x z
namespace Path
def concat {A : Type u} {x y z : A} : Path x y → Path y z → Path x z
  | .nil _, q => q
  | .seq s p, q => .seq s (concat p q)
infixr:65 " ++ₚ " => concat
def lEmbed {A : Type u} {x y : A} (s : Step x y) : Path x y :=
  .seq s (.nil y)
def inv {A : Type u} {x y : A} : Path x y → Path y x
  | .nil _ => .nil _
  | .seq s p => inv p ++ₚ lEmbed (.sym s)
def ap {A B : Type u} (f : A → B) {x y : A} : Path x y → Path (f x) (f y)
  | .nil _ => .nil _
  | .seq s p => .seq (.apCong f s) (ap f p)
def toStep {A : Type u} {x y : A} : Path x y → Step x y
  | .nil _ => .refl _
  | .seq s p => .trans s (toStep p)
end Path
def etaExpand {A B : Type u} (f : A → B) : A → B := fun x => f x
inductive Step2 : {A : Type u} → {x y : A} → Path x y → Path x y → Type (u + 1) where
  | cReflStep {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.refl x) ++ₚ Path.lEmbed s)
        (Path.lEmbed s ++ₚ Path.lEmbed (.refl y))
  | betaStep {A B : Type u} (f : A → B) {a b : A} (s : Step a b) :
      Step2 (Path.ap (fun x => f x) (Path.lEmbed s) ++ₚ Path.lEmbed (.beta f b))
        (Path.lEmbed (.beta f a) ++ₚ Path.ap f (Path.lEmbed s))
  | etaStep {A B : Type u} {f g : A → B} (s : Step f g) :
      Step2 (Path.ap etaExpand (Path.lEmbed s) ++ₚ Path.lEmbed (.eta g))
        (Path.lEmbed (.eta f) ++ₚ Path.lEmbed s)
  | lamCongStep {A B : Type u} {f g : A → B}
      (h : (x : A) → Step (f x) (g x)) {a b : A} (s : Step a b) :
      Step2
        (Path.ap f (Path.lEmbed s) ++ₚ
          Path.lEmbed (.apCong (fun k : A → B => k b) (.lamCong h)))
        (Path.lEmbed (.apCong (fun k : A → B => k a) (.lamCong h)) ++ₚ
          Path.ap g (Path.lEmbed s))
  | refl2 {A : Type u} {x y : A} (p : Path x y) : Step2 p p
  | sym2 {A : Type u} {x y : A} {p q : Path x y} : Step2 p q → Step2 q p
  | trans2 {A : Type u} {x y : A} {p q r : Path x y} :
      Step2 p q → Step2 q r → Step2 p r
  | reflStep2 {A : Type u} (x : A) :
      Step2 (Path.lEmbed (.refl x)) (.nil x)
  | symStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.sym s)) (Path.inv (Path.lEmbed s))
  | transStep2 {A : Type u} {x y z : A} (s : Step x y) (t : Step y z) :
      Step2 (Path.lEmbed (.trans s t)) (Path.lEmbed s ++ₚ Path.lEmbed t)
  | leftInvStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.inv (Path.lEmbed s) ++ₚ Path.lEmbed s) (.nil y)
  | rightInvStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed s ++ₚ Path.inv (Path.lEmbed s)) (.nil x)
  | symSymStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.sym (.sym s))) (Path.lEmbed s)
  | apCongIdStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.ap (fun t => t) (Path.lEmbed s)) (Path.lEmbed s)
  | apCongStep2 {A B : Type u} (f : A → B) {x y : A} {p q : Path x y} :
      Step2 p q → Step2 (Path.ap f p) (Path.ap f q)
  | apCongComposeStep2 {A B C : Type u} (g : B → C) (f : A → B)
      {x y : A} (s : Step x y) :
      Step2 (Path.ap g (Path.ap f (Path.lEmbed s)))
        (Path.ap (fun z => g (f z)) (Path.lEmbed s))
  | cong2 {A : Type u} {x y z : A} (s : Step x y) {p q : Path y z} :
      Step2 p q → Step2 (.seq s p) (.seq s q)
  | whiskR2 {A : Type u} {w x y : A} {p q : Path w x} :
      Step2 p q → (r : Path x y) → Step2 (p ++ₚ r) (q ++ₚ r)
inductive Path2 {A : Type u} {x y : A} : (p q : Path x y) → Type (u + 1) where
  | nil2 (p : Path x y) : Path2 p p
  | seq2 {p q r : Path x y} : Step2 p q → Path2 q r → Path2 p r
namespace Step2
def whiskL {A : Type u} {w x y : A} :
    (r : Path w x) → {p q : Path x y} →
      Step2 p q → Step2 (r ++ₚ p) (r ++ₚ q)
  | .nil _, _, _, cell => cell
  | .seq s r, _, _, cell => .cong2 s (whiskL r cell)
def rightId {A : Type u} {x y : A} :
    (p : Path x y) → Step2 (p ++ₚ .nil y) p
  | .nil _ => .refl2 _
  | .seq s p => .cong2 s (rightId p)
def assoc {A : Type u} {w x y z : A} :
    (p : Path w x) → (q : Path x y) → (r : Path y z) →
      Step2 ((p ++ₚ q) ++ₚ r) (p ++ₚ (q ++ₚ r))
  | .nil _, _, r => .refl2 _
  | .seq s p, q, r => .cong2 s (assoc p q r)
def horizontal {A : Type u} {x y z : A} {p₁ q₁ : Path x y}
    {p₂ q₂ : Path y z} (first : Step2 p₁ q₁) (second : Step2 p₂ q₂) :
    Step2 (p₁ ++ₚ p₂) (q₁ ++ₚ q₂) :=
  .trans2 (.whiskR2 first p₂) (whiskL q₁ second)
def cRefl {A : Type u} {x y : A} :
    (p : Path x y) →
      Step2 (Path.lEmbed (.refl x) ++ₚ p) (p ++ₚ Path.lEmbed (.refl y))
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2 (.whiskR2 (.cReflStep s) p)
        (whiskL (Path.lEmbed s) (cRefl p))
def pathToStepCoherence {A : Type u} {x y : A} :
    (p : Path x y) → Step2 (Path.lEmbed (Path.toStep p)) p
  | .nil x => .reflStep2 x
  | .seq s p =>
      .trans2 (.transStep2 s (Path.toStep p))
        (whiskL (Path.lEmbed s) (pathToStepCoherence p))
def betaPath {A B : Type u} (f : A → B) {x y : A} :
    (p : Path x y) → Step2
      (Path.ap (fun a => f a) p ++ₚ Path.lEmbed (.beta f y))
      (Path.lEmbed (.beta f x) ++ₚ Path.ap f p)
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (whiskL (Path.lEmbed (.apCong (fun a => f a) s)) (betaPath f p))
        (.whiskR2 (.betaStep f s) (Path.ap f p))
def etaPath {A B : Type u} {f g : A → B} (p : Path f g) :
    Step2
      (Path.ap etaExpand p ++ₚ Path.lEmbed (.eta g))
      (Path.lEmbed (.eta f) ++ₚ p) := by
  let coherence := pathToStepCoherence p
  exact .trans2
    (.whiskR2 (.sym2 (.apCongStep2 etaExpand coherence)) (Path.lEmbed (.eta g)))
    (.trans2 (.etaStep (Path.toStep p))
      (whiskL (Path.lEmbed (.eta f)) coherence))
def lamCongPath {A B : Type u} {f g : A → B}
    (h : (x : A) → Step (f x) (g x)) {x y : A} :
    (p : Path x y) → Step2
      (Path.ap f p ++ₚ
        Path.lEmbed (.apCong (fun k : A → B => k y) (.lamCong h)))
      (Path.lEmbed (.apCong (fun k : A → B => k x) (.lamCong h)) ++ₚ
        Path.ap g p)
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (whiskL (Path.lEmbed (.apCong f s)) (lamCongPath h p))
        (.whiskR2 (.lamCongStep h s) (Path.ap g p))
def apId {A : Type u} {x y : A} :
    (p : Path x y) → Step2 (Path.ap (fun t => t) p) p
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (.whiskR2 (.apCongIdStep2 s) (Path.ap (fun t => t) p))
        (whiskL (Path.lEmbed s) (apId p))
def apCompose {A B C : Type u} (g : B → C) (f : A → B)
    {x y : A} : (p : Path x y) →
    Step2 (Path.ap g (Path.ap f p)) (Path.ap (fun z => g (f z)) p)
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (.whiskR2 (.apCongComposeStep2 g f s) (Path.ap g (Path.ap f p)))
        (whiskL (Path.lEmbed (.apCong (fun z => g (f z)) s)) (apCompose g f p))
def apConcat {A B : Type u} (f : A → B) {x y z : A} :
    (p : Path x y) → (q : Path y z) →
      Step2 (Path.ap f (p ++ₚ q)) (Path.ap f p ++ₚ Path.ap f q)
  | .nil _, q => .refl2 _
  | .seq s p, q => .cong2 (.apCong f s) (apConcat f p q)
def reverseNaturality {A B : Type u} {f g : A → B}
    (h : (x : A) → Step (f x) (g x)) {x y : A} (p : Path x y)
    (cell : Step2
      (Path.ap f p ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g p)) :
    Step2
      (Path.ap g p ++ₚ Path.lEmbed (.sym (h y)))
      (Path.lEmbed (.sym (h x)) ++ₚ Path.ap f p) := by
  let hx := Path.lEmbed (h x)
  let hy := Path.lEmbed (h y)
  let ihx := Path.inv hx
  let ihy := Path.inv hy
  let fp := Path.ap f p
  let gp := Path.ap g p
  exact .trans2
    (.whiskR2 (.sym2 (.leftInvStep2 (h x))) (gp ++ₚ ihy))
    (.trans2 (assoc ihx hx (gp ++ₚ ihy))
      (.trans2 (whiskL ihx (.sym2 (assoc hx gp ihy)))
        (.trans2 (whiskL ihx (.whiskR2 (.sym2 cell) ihy))
          (.trans2 (whiskL ihx (assoc fp hy ihy))
            (.trans2 (whiskL ihx (whiskL fp (.rightInvStep2 (h y))))
              (whiskL ihx (rightId fp)))))))
def transNaturality {A B : Type u} {f g k : A → B}
    (h : (x : A) → Step (f x) (g x))
    (d : (x : A) → Step (g x) (k x)) {x y : A} (p : Path x y)
    (first : Step2
      (Path.ap f p ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g p))
    (second : Step2
      (Path.ap g p ++ₚ Path.lEmbed (d y))
      (Path.lEmbed (d x) ++ₚ Path.ap k p)) :
    Step2
      (Path.ap f p ++ₚ Path.lEmbed (.trans (h y) (d y)))
      (Path.lEmbed (.trans (h x) (d x)) ++ₚ Path.ap k p) := by
  let fp := Path.ap f p
  let gp := Path.ap g p
  let kp := Path.ap k p
  let hx := Path.lEmbed (h x)
  let hy := Path.lEmbed (h y)
  let dx := Path.lEmbed (d x)
  let dy := Path.lEmbed (d y)
  exact .trans2
    (whiskL fp (.transStep2 (h y) (d y)))
    (.trans2 (.sym2 (assoc fp hy dy))
      (.trans2 (.whiskR2 first dy)
        (.trans2 (assoc hx gp dy)
          (.trans2 (whiskL hx second)
            (.trans2 (.sym2 (assoc hx dx kp))
              (.whiskR2 (.sym2 (.transStep2 (h x) (d x))) kp))))))
def mapNaturality {A B C : Type u} (v : B → C)
    {f g : A → B} (h : (x : A) → Step (f x) (g x))
    {x y : A} (p : Path x y)
    (cell : Step2
      (Path.ap f p ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g p)) :
    Step2
      (Path.ap (fun z => v (f z)) p ++ₚ Path.lEmbed (.apCong v (h y)))
      (Path.lEmbed (.apCong v (h x)) ++ₚ Path.ap (fun z => v (g z)) p) := by
  let fp := Path.ap f p
  let gp := Path.ap g p
  let vfp := Path.ap v fp
  let vgp := Path.ap v gp
  exact .trans2
    (.whiskR2 (.sym2 (apCompose v f p)) (Path.lEmbed (.apCong v (h y))))
    (.trans2 (.sym2 (apConcat v fp (Path.lEmbed (h y))))
      (.trans2 (.apCongStep2 v cell)
        (.trans2 (apConcat v (Path.lEmbed (h x)) gp)
          (whiskL (Path.lEmbed (.apCong v (h x))) (apCompose v g p)))))
end Step2
inductive HomotopyStepI : {A B : Type u} → (A → B) → (A → B) → Type (u + 1) where
  | refl {A B : Type u} (f : A → B) : HomotopyStepI f f
  | beta {A B : Type u} (f : A → B) : HomotopyStepI (fun x => f x) f
  | eta {A B : Type u} :
      HomotopyStepI (@etaExpand A B) (fun f => f)
  | apCong {A B C : Type u} (v : B → C) {f g : A → B} :
      HomotopyStepI f g →
      HomotopyStepI (fun x => v (f x)) (fun x => v (g x))
  | sym {A B : Type u} {f g : A → B} :
      HomotopyStepI f g → HomotopyStepI g f
  | trans {A B : Type u} {f g k : A → B} :
      HomotopyStepI f g → HomotopyStepI g k → HomotopyStepI f k
  | lamCong {A B : Type u} {f g : A → B} :
      HomotopyStepI f g → HomotopyStepI f g
structure CertifiedStepEvaluation {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) : Type (u + 1) where
  family : (x : A) → Step (f x) (g x)
  naturality : {x y : A} → (p : Path x y) →
    Step2
      (Path.ap f p ++ₚ Path.lEmbed (family y))
      (Path.lEmbed (family x) ++ₚ Path.ap g p)
def evalHomotopyStepI {A B : Type u} {f g : A → B} :
    (e : HomotopyStepI f g) → CertifiedStepEvaluation e
  | .refl f =>
      {
        family := fun x => .refl (f x)
        naturality := fun p => .sym2 (Step2.cRefl (Path.ap f p))
      }
  | .beta f =>
      {
        family := fun x => .beta f x
        naturality := fun p => Step2.betaPath f p
      }
  | @HomotopyStepI.eta A B =>
      {
        family := fun f => .eta f
        naturality := fun p =>
          .trans2 (Step2.etaPath p)
            (Step2.whiskL (Path.lEmbed (.eta _)) (.sym2 (Step2.apId p)))
      }
  | .apCong v e =>
      {
        family := fun x => .apCong v ((evalHomotopyStepI e).family x)
        naturality := fun p => Step2.mapNaturality v (evalHomotopyStepI e).family p
          ((evalHomotopyStepI e).naturality p)
      }
  | .sym e =>
      {
        family := fun x => .sym ((evalHomotopyStepI e).family x)
        naturality := fun p => Step2.reverseNaturality (evalHomotopyStepI e).family p
          ((evalHomotopyStepI e).naturality p)
      }
  | .trans first second =>
      {
        family := fun x => .trans ((evalHomotopyStepI first).family x)
          ((evalHomotopyStepI second).family x)
        naturality := fun p =>
          Step2.transNaturality (evalHomotopyStepI first).family
            (evalHomotopyStepI second).family p
            ((evalHomotopyStepI first).naturality p)
            ((evalHomotopyStepI second).naturality p)
      }
  | .lamCong e =>
      {
        family := fun x =>
          .apCong (fun k => k x) (.lamCong (evalHomotopyStepI e).family)
        naturality := fun p => Step2.lamCongPath (evalHomotopyStepI e).family p
      }
def certifiedStepNaturality {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Step2
      (Path.ap f p ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ Path.ap g p) :=
  (evalHomotopyStepI e).naturality p
inductive HomotopyPathI : {A B : Type u} → (A → B) → (A → B) → Type (u + 1) where
  | nil {A B : Type u} (f : A → B) : HomotopyPathI f f
  | seq {A B : Type u} {f g k : A → B} :
      HomotopyStepI f g → HomotopyPathI g k → HomotopyPathI f k
def evalHomotopyPathI {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → (x : A) → Path (f x) (g x)
  | .nil f, x => .nil (f x)
  | .seq e hp, x =>
      .seq ((evalHomotopyStepI e).family x) (evalHomotopyPathI hp x)
def evaluatedPathNaturalityCell {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → (p : Path x y) →
    Step2
      (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p)
  | .nil f, _, _, p => Step2.rightId (Path.ap f p)
  | @HomotopyPathI.seq _ _ f g k e hp, x, y, p =>
      let ev := evalHomotopyStepI e
      let fp := Path.ap f p
      let gp := Path.ap g p
      let kp := Path.ap k p
      let hx := Path.lEmbed (ev.family x)
      let hy := Path.lEmbed (ev.family y)
      let rx := evalHomotopyPathI hp x
      let ry := evalHomotopyPathI hp y
      .trans2 (.sym2 (Step2.assoc fp hy ry))
        (.trans2 (.whiskR2 (ev.naturality p) ry)
          (.trans2 (Step2.assoc hx gp ry)
            (.trans2 (Step2.whiskL hx (evaluatedPathNaturalityCell hp p))
              (.sym2 (Step2.assoc hx rx kp)))))
namespace Path2
def singleton {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) : Path2 p q := .seq2 cell (.nil2 q)
def toCell {A : Type u} {x y : A} {p q : Path x y} :
    (cells : Path2 p q) → Step2 p q
  | .nil2 p => .refl2 p
  | .seq2 cell cells => .trans2 cell (toCell cells)
def whiskL {A : Type u} {w x y : A} (r : Path w x) {p q : Path x y} :
    (cells : Path2 p q) → Path2 (r ++ₚ p) (r ++ₚ q)
  | .nil2 p => .nil2 _
  | .seq2 cell cells => .seq2 (Step2.whiskL r cell) (whiskL r cells)
def whiskR {A : Type u} {x y z : A} {p q : Path x y} :
    (cells : Path2 p q) → (r : Path y z) → Path2 (p ++ₚ r) (q ++ₚ r)
  | .nil2 p, r => .nil2 _
  | .seq2 cell cells, r => .seq2 (.whiskR2 cell r) (whiskR cells r)
end Path2
def certifiedPathNaturality {A B : Type u} {f g : A → B}
    (hp : HomotopyPathI f g) {x y : A} (p : Path x y) :
    Path2
      (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p) :=
  Path2.singleton (evaluatedPathNaturalityCell hp p)
def transportAlongPresented {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x y : A) (q : Path (f x) (f y)) :
    Path (g x) (g y) :=
  let ev := evalHomotopyStepI e
  Path.inv (Path.lEmbed (ev.family x)) ++ₚ
    (q ++ₚ Path.lEmbed (ev.family y))
def transportAlongPresentedRespects {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} {q r : Path (f x) (f y)}
    (cells : Path2 q r) :
    Path2 (transportAlongPresented e x y q) (transportAlongPresented e x y r) :=
  let ev := evalHomotopyStepI e
  Path2.whiskL (Path.inv (Path.lEmbed (ev.family x)))
    (Path2.whiskR cells (Path.lEmbed (ev.family y)))
def certifiedTransportCell {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Step2 (transportAlongPresented e x y (Path.ap f p)) (Path.ap g p) := by
  let ev := evalHomotopyStepI e
  let hx := Path.lEmbed (ev.family x)
  let hy := Path.lEmbed (ev.family y)
  let ihx := Path.inv hx
  let fp := Path.ap f p
  let gp := Path.ap g p
  exact .trans2 (Step2.whiskL ihx (ev.naturality p))
    (.trans2 (.sym2 (Step2.assoc ihx hx gp))
      (.whiskR2 (.leftInvStep2 (ev.family x)) gp))
def certifiedTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Path2 (transportAlongPresented e x y (Path.ap f p)) (Path.ap g p) :=
  Path2.singleton (certifiedTransportCell e p)
def recoverNaturalityFromTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} {q : Path (f x) (f y)}
    {r : Path (g x) (g y)}
    (cells : Path2 (transportAlongPresented e x y q) r) :
    Path2
      (q ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ r) := by
  let ev := evalHomotopyStepI e
  let hx := Path.lEmbed (ev.family x)
  let ihx := Path.inv hx
  let source := q ++ₚ Path.lEmbed (ev.family y)
  exact Path2.singleton
    (.trans2 (.whiskR2 (.sym2 (.rightInvStep2 (ev.family x))) source)
      (.trans2 (Step2.assoc hx ihx source)
        (Step2.whiskL hx (Path2.toCell cells))))
def certifiedNaturalityViaTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Path2
      (Path.ap f p ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ Path.ap g p) :=
  recoverNaturalityFromTransport e (certifiedTransport e p)
def transportAlongPathI {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → (x y : A) →
    Path (f x) (f y) → Path (g x) (g y)
  | .nil _, _, _, q => q
  | .seq e hp, x, y, q =>
      transportAlongPathI hp x y (transportAlongPresented e x y q)
def transportAlongPathIRespects {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → {q r : Path (f x) (f y)} →
    Path2 q r →
    Path2 (transportAlongPathI hp x y q) (transportAlongPathI hp x y r)
  | .nil _, _, _, _, _, cells => cells
  | .seq e hp, _, _, _, _, cells =>
      transportAlongPathIRespects hp (transportAlongPresentedRespects e cells)
def certifiedPathTransport {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → (p : Path x y) →
    Path2 (transportAlongPathI hp x y (Path.ap f p)) (Path.ap g p)
  | .nil _, _, _, p => .nil2 _
  | .seq e hp, _, _, p =>
      Path2.singleton (.trans2
        (Path2.toCell (transportAlongPathIRespects hp (certifiedTransport e p)))
        (Path2.toCell (certifiedPathTransport hp p)))
def recoverNaturalityFromPathTransport {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} →
    {q : Path (f x) (f y)} → {r : Path (g x) (g y)} →
    Path2 (transportAlongPathI hp x y q) r →
    Path2 (q ++ₚ evalHomotopyPathI hp y) (evalHomotopyPathI hp x ++ₚ r)
  | .nil _, _, _, q, _, cells =>
      Path2.singleton (.trans2 (Step2.rightId q) (Path2.toCell cells))
  | .seq e hp, x, y, q, r, cells =>
      let hx := Path.lEmbed ((evalHomotopyStepI e).family x)
      let hy := Path.lEmbed ((evalHomotopyStepI e).family y)
      let rx := evalHomotopyPathI hp x
      let ry := evalHomotopyPathI hp y
      let tq := transportAlongPresented e x y q
      let first := Path2.toCell (recoverNaturalityFromTransport e (.nil2 tq))
      let rest := Path2.toCell (recoverNaturalityFromPathTransport hp cells)
      Path2.singleton (.trans2 (.sym2 (Step2.assoc q hy ry))
        (.trans2 (.whiskR2 first ry)
          (.trans2 (Step2.assoc hx tq ry)
            (.trans2 (Step2.whiskL hx rest) (.sym2 (Step2.assoc hx rx r))))))
def certifiedPathNaturalityViaTransport {A B : Type u} {f g : A → B}
    (hp : HomotopyPathI f g) {x y : A} (p : Path x y) :
    Path2 (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p) :=
  recoverNaturalityFromPathTransport hp (certifiedPathTransport hp p)
namespace Step
def headTag {A : Type u} {x y : A} : Step x y → Nat
  | @TDLC.Step.beta _ _ f a => 0
  | @TDLC.Step.eta _ _ f => 1
  | @TDLC.Step.apCong _ _ f _ _ s => 2
  | @TDLC.Step.lamCong _ _ f g h => 3
  | @TDLC.Step.refl _ x => 4
  | @TDLC.Step.sym _ _ _ s => 5
  | @TDLC.Step.trans _ _ _ _ s t => 6
end Step
def mixedUnitFamily : (b : Bool) → Step Unit.unit Unit.unit
  | false => .beta (fun x : Unit => x) Unit.unit
  | true => .refl Unit.unit
def bxor : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false
namespace Step
def parity {A : Type u} {x y : A} : Step x y → Bool
  | @TDLC.Step.beta _ _ f a => true
  | @TDLC.Step.eta _ _ f => false
  | @TDLC.Step.apCong _ _ f _ _ s => parity s
  | @TDLC.Step.lamCong _ _ f g h => false
  | @TDLC.Step.refl _ x => false
  | @TDLC.Step.sym _ _ _ s => parity s
  | @TDLC.Step.trans _ _ _ _ s t => bxor (parity s) (parity t)
end Step
namespace Path
def parity {A : Type u} {x y : A} : Path x y → Bool
  | .nil _ => false
  | .seq s p => bxor (Step.parity s) (parity p)
end Path
end TDLC


